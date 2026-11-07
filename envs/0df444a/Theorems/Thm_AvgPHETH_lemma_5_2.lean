-- Prove2me | Theorems.Thm_AvgPHETH_lemma_5_2
-- name    : AvgPHETH.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:11.1413+00:00
-- url     : https://prove2.me/theorems/6d715d66-6093-4b03-90be-4362bc5daffb
-- title:
--   Lemma 5.2 — amortized bound by computational depth, with input cost $2|z|$
-- statement:
--   Let the query and response lengths be $m(n),\ell(n)\ge1$, and let $f_n(z,q)\in\{0,1\}^{\ell(n)}$ be computed by one machine with oracle $O\oplus A$, $A\in\Sigma_d^{p,O}$, $d\ge1$, uniformly in $n$, $z\in\{0,1\}^{\le\mathrm{poly}(n)}$ and $q\in\{0,1\}^{m}$, within $\mathrm{time}_f(n,|z|)$ steps. Assume $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$. There are a constant $c\ge2$ and a polynomial $p$ such that for every $z$ and every query sequence $\boldsymbol q=(q_1,\dots,q_R)\in(\{0,1\}^m)^R$ with $R\ge1$, setting $a_i=f_n(z,q_i)$ and $\tau_{<i}=(q_1,a_1,\dots,q_{i-1},a_{i-1})$ gives
--
--   $$\sum_{i=1}^R K^{t^c,O}(a_i\mid\tau_{<i},q_i)\le \mathrm{cd}^{t,t^c}(\boldsymbol q)+2|z|+R\cdot O(\log t)$$
--
--   whenever $t\ge p(n,|z|,R,m,\mathrm{time}_f(n,|z|))$, where $\mathrm{cd}^{t,t^c}(\boldsymbol q)=K^{t,O}(\boldsymbol q)-K^{t^c,O}(\boldsymbol q)$ is the computational depth. The constant in $O(\cdot)$ is independent of $R,n,z,\boldsymbol q,t$.
--
--   The total description length of the responses is charged to the depth of the query sequence, and the input costs only $2|z|$ in total.
--
--   Differences from the source:
--   - generalization: the unrelativized statement under $\mathrm{Dist}\Sigma_{d+1}^p\subseteq\mathrm{AvgP}$ → relative to every oracle $O$, under $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$; reason: Remark 6.4 (p.28) and p.30 relativize it and weaken the hypothesis; at $O=\emptyset$ the footnote on p.10 gives the hypothesis from the printed one
--   - generalization: an efficient universal machine $U$, fixed once → every $U$ with polynomial overhead (IsEfficientUniversal); reason: the page prints no overhead bound; the usual efficient machines have polynomial overhead, so this specializes to any of them
--   - encoding: oracle access to $A$ → oracle $O\oplus A$; reason: at $O=\emptyset$ the tag on each query is the only change, with polynomial overhead
--   - encoding: $\mathrm{cd}^{t,t^c}(\boldsymbol q)$ on the right → $K^{t^c,O}(\boldsymbol q)$ moved to the left, no subtraction in $\mathbb N\cup\{\infty\}$; reason: for such $t$, $K^{t^c,O}(\boldsymbol q)\le K^{t,O}(\boldsymbol q)<\infty$, so it is the printed inequality
--   - reading: "for every $z$" → $|z|\le r(n)$, with $r$ a polynomial; reason: the section preamble defines $f_n$ on $z\in\{0,1\}^{\le\mathrm{poly}(n)}$ only
--   - encoding: a polynomial $p(n,|z|,R,m,\mathrm{time}_f)$ → $(n+|z|+R+m+\mathrm{time}_f+2)^e+e$; reason: every polynomial is bounded by one of this form
--   - encoding: the condition $(\tau_{<i},q_i)$ and the tuple $\boldsymbol q$ → binTuple of the flat tuple $(q_1,a_1,\dots,q_{i-1},a_{i-1},q_i)$ and of $(q_1,\dots,q_R)$; reason: the page fixes some encoding of tuples (p.18), and the flat transcript is generated in polynomial time from $\langle\tau_{<i},q_i\rangle$ (p.21)
--   - encoding: sums of $K^t$ values and $\log t$ → sums in $\mathbb R_{\ge0}\cup\{\infty\}$ with $K^t=\infty$ when no program exists; base-2 logarithm; reason: Lean convention; a finite value is unchanged
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.2, p.20 (PDF 22)

import Mathlib
import Definitions.Def_AvgPHETH_IsEfficientUniversal
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_Kt
import Definitions.Def_AvgPHETH_oJoin
import Definitions.Def_AvgPHETH_IsRespFamily
import Definitions.Def_AvgPHETH_transcript
import Definitions.Def_AvgPHETH_binTuple
open KarpLiptonOM
open scoped ENNReal

namespace AvgPHETH

/-- **Lemma 5.2** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.20 (PDF 22)), relative to every oracle `O` (Remark 6.4, p.28 (PDF 30); p.30 (PDF 32)). With
query and response lengths `m(n), ℓ(n) ≥ 1` and `f_n(z, q)` computed with oracle access to `O ⊕ A`, `A ∈ Σ_d^{p,O}`, `d ≥ 1`, in
time at most `time_f(n, |z|)`: if `Σ_{d+1}^{p,O} × {U, T} ⊆ AvgP^O`, there are `c ≥ 2` and a polynomial `p` such that for every
`z` and `q = (q₁, …, q_R) ∈ ({0,1}^m)^R` with `R ≥ 1`, with `a_i = f_n(z, q_i)` and `τ_{<i} = (q₁, a₁, …, q_{i−1}, a_{i−1})`,
`∑_i K^{t^c}(a_i | τ_{<i}, q_i) ≤ cd^{t,t^c}(q) + 2|z| + R · O(log t)` whenever `t ≥ p(n, |z|, R, m, time_f(n, |z|))`.

**Formalization Note** `cd^{t,t^c}(q) = K^t(q) − K^{t^c}(q)`, and the term `K^{t^c}(q)` is moved to the left, so that no subtraction
in `ℕ∞` occurs; for such `t`, `K^{t^c}(q) ≤ K^t(q) < ∞`, so this is the printed inequality. `p` is written `(n + |z| + R + m + time_f + 2)^e + e`, the
constant of `O(·)` is the named `C`, and `C` does not depend on `R, n, z, q, t`. -/
theorem lemma_5_2 (U : OracleTM) (hU : IsEfficientUniversal U) (O : Set (List Bool)) (d : ℕ)
    (hd : 1 ≤ d) (hAvg : TimesUT O (SigmaPO O (d + 1))) (A : Set (List Bool))
    (hA : A ∈ SigmaPO O d) (m ℓ : ℕ → ℕ) (timef : ℕ → ℕ → ℕ) (r : Polynomial ℕ) (M : OracleTM)
    (hm : ∀ n, 1 ≤ m n) (hℓ : ∀ n, 1 ≤ ℓ n) (hf : IsRespFamily M (oJoin O A) timef m ℓ r) :
    ∃ c e C : ℕ, 2 ≤ c ∧ ∀ (n : ℕ) (z : List Bool), z.length ≤ r.eval n →
      ∀ (R : ℕ), 1 ≤ R → ∀ q : Fin R → List Bool, (∀ i, (q i).length = m n) →
      ∀ t : ℕ, (n + z.length + R + m n + timef n z.length + 2) ^ e + e ≤ t →
        ∑ i : Fin R, ((Kt U O (t ^ c) (resp M (oJoin O A) timef n z (q i))
              (transcript (resp M (oJoin O A) timef n z) q i) : ℕ∞) : ℝ≥0∞) +
            ((Kt U O (t ^ c) (binTuple (List.ofFn q)) [] : ℕ∞) : ℝ≥0∞) ≤
          ((Kt U O t (binTuple (List.ofFn q)) [] : ℕ∞) : ℝ≥0∞) + 2 * (z.length : ℝ≥0∞) +
            ENNReal.ofReal ((R : ℝ) * (C : ℝ) * Real.logb 2 t) := by sorry

end AvgPHETH
