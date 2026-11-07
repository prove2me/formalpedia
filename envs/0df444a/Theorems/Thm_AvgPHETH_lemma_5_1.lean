-- Prove2me | Theorems.Thm_AvgPHETH_lemma_5_1
-- name    : AvgPHETH.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:19.738684+00:00
-- url     : https://prove2.me/theorems/51626143-feaa-4d05-93df-15bea527bb0e
-- title:
--   Lemma 5.1 — a polynomial-size sample list compresses every response to $\mathcal L_{\downarrow1}(m)$
-- statement:
--   Fix $d\ge1$ and constants $0<\alpha<\beta<1$. Let $m(n)=n^{\Theta(1)}$ and $\ell(n)\ge1$ be length functions computable in time $\mathrm{poly}(n)$. Suppose a family $f_n(z,q)\in\{0,1\}^{\ell(n)}$ is uniformly computable, for all $n$, $z\in\{0,1\}^{\le\mathrm{poly}(n)}$ and $q\in\{0,1\}^{m(n)}$, using a fixed oracle $A\in\Sigma_d^{p,O}$ (and $O$) in time $2^{O(n^\alpha)}$. Assume $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$. Then there is a length function $\ell'\in\mathcal L_{\downarrow1}(m(n))$ such that, for every sufficiently large $n$ and every $z\in\{0,1\}^{\le\mathrm{poly}(n)}$, there is a sample list $S_z\subseteq\{(q,f_n(z,q)):q\in\{0,1\}^{m(n)}\}$ of size bounded by $\mathrm{poly}(n)$ such that, for every $q\in\{0,1\}^{m(n)}$,
--
--   $$K^{2^{n^\beta},O}(f_n(z,q)\mid n,S_z,q)\le\ell'(n).$$
--
--   The bound is independent of the length of the auxiliary input $z$, which may be incompressible. This is the main technical lemma of the paper.
--
--   Differences from the source:
--   - generalization: the unrelativized statement under $\mathrm{Dist}\Sigma_{d+1}^p\subseteq\mathrm{AvgP}$ → relative to every oracle $O$, under $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$; reason: Remark 6.4 (p.28) and p.30 relativize it and weaken the hypothesis; at $O=\emptyset$ the footnote on p.10 gives the hypothesis from the printed one
--   - generalization: an efficient universal machine $U$, fixed once → every $U$ with polynomial overhead (IsEfficientUniversal); reason: the page prints no overhead bound; the usual efficient machines have polynomial overhead, so this specializes to any of them
--   - encoding: oracle access to $A$ → oracle $O\oplus A$; reason: at $O=\emptyset$ the tag on each query is the only change, with polynomial overhead
--   - encoding: the condition $(n,S_z,q)$ → the flat tuple $(1^n,q_1,a_1,\dots,q_s,a_s,q)$ under binTuple; reason: the forms convert into each other within the time bound, at a constant cost absorbed in $\ell'$
--   - encoding: time $2^{O(n^\alpha)}$ → $\lceil2^{Cn^\alpha}\rceil+C$; reason: the summand only matters for small $n$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.1, p.19 (PDF 21)

import Mathlib
import Definitions.Def_AvgPHETH_IsEfficientUniversal
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_Kt
import Definitions.Def_AvgPHETH_oJoin
import Definitions.Def_AvgPHETH_IsRespFamily
import Definitions.Def_AvgPHETH_IsPolyLen
import Definitions.Def_AvgPHETH_PolyTheta
import Definitions.Def_AvgPHETH_LDown
import Definitions.Def_AvgPHETH_expTime
import Definitions.Def_AvgPHETH_binTuple
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM
open scoped ENNReal

namespace AvgPHETH

/-- **Lemma 5.1** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.19 (PDF 21)), relative to every oracle `O` (Remark 6.4, p.28 (PDF 30); p.30 (PDF 32)). Fix `d ≥ 1` and
`0 < α < β < 1`. Let `m(n) = n^{Θ(1)}` and `ℓ(n) ≥ 1` be length functions computable in time `poly(n)`, and let `f_n(z, q) ∈ {0,1}^{ℓ(n)}` be
uniformly computable, for `z ∈ {0,1}^{≤ poly(n)}` and `q ∈ {0,1}^{m(n)}`, with a fixed oracle `A ∈ Σ_d^{p,O}` (and `O`) in time `2^{O(n^α)}`. Assume
`Σ_{d+1}^{p,O} × {U, T} ⊆ AvgP^O`. Then there is `ℓ' ∈ 𝓛_{↓1}(m(n))` such that, for every sufficiently large `n` and every
`z ∈ {0,1}^{≤ poly(n)}`, there is a sample list `S_z ⊆ {(q, f_n(z, q))}` of size bounded by `poly(n)` such that, for every `q ∈ {0,1}^{m(n)}`,
`K^{2^{n^β}}(f_n(z, q) | n, S_z, q) ≤ ℓ'(n)`.

**Formalization Note** `ℓ'` and the size polynomial come before `z`. The condition is the flat tuple `(1^n, q₁, a₁, …, q_s, a_s, q)` under `binTuple`.
`K^t` is relative to `O`; at `O = ∅` this is the printed `K^t`. -/
theorem lemma_5_1 (U : OracleTM) (hU : IsEfficientUniversal U) (O : Set (List Bool)) (d : ℕ)
    (hd : 1 ≤ d) (hAvg : TimesUT O (SigmaPO O (d + 1))) (A : Set (List Bool))
    (hA : A ∈ SigmaPO O d) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (m ℓ : ℕ → ℕ) (r : Polynomial ℕ) (M : OracleTM) (C : ℕ)
    (hmθ : PolyTheta m) (hm : IsPolyLen m) (hℓ : IsPolyLen ℓ) (hℓ1 : ∀ n, 1 ≤ ℓ n)
    (hf : IsRespFamily M (oJoin O A) (fun n _ => expTime C α n) m ℓ r) :
    ∃ ℓ' ∈ LDown 1 m, ∃ (s : Polynomial ℕ) (n₀ : ℕ), ∀ n ≥ n₀, ∀ z : List Bool,
      z.length ≤ r.eval n →
      ∃ S : List (List Bool × List Bool), S.length ≤ s.eval n ∧
        (∀ p ∈ S, p.1.length = m n ∧ p.2 = resp M (oJoin O A) (fun n _ => expTime C α n) n z p.1) ∧
        ∀ q : List Bool, q.length = m n →
          Kt U O ⌈(2 : ℝ) ^ ((n : ℝ) ^ β)⌉₊ (resp M (oJoin O A) (fun n _ => expTime C α n) n z q)
            (binTuple ([unary n] ++ S.flatMap (fun p => [p.1, p.2]) ++ [q])) ≤ (ℓ' n : ℕ∞) := by sorry

end AvgPHETH
