-- Prove2me | Theorems.Thm_CertRandQROM_lemma_7_3_low_entropy_heavy
-- name    : CertRandQROM.lemma_7_3_low_entropy_heavy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:48.245436+00:00
-- url     : https://prove2.me/theorems/94ff27df-66b1-41a2-84d8-a82561259433
-- title:
--   Lemma 7.3 — a likely correct answer with $s$ lightly queried symbols has probability at most $2(1-p)^s$
-- statement:
--   Let $\alpha\in(0,1]$, $p\in(0,1)$ and $s\in[n]$, let $H$ be a $p$-biased oracle on $[n]\times\Sigma$, and let $(H,X)$ be sampled by $H\leftarrow$ the $p$-biased law and $X\leftarrow\mathcal A^H$. The probability that $(H,X)=(h,x)$ satisfies all of
--
--   1. there is $I\subseteq[n]$, $|I|=s$, with $\tilde w_{i,x_i}(h)<\alpha/(4n)$ for all $i\in I$;
--   2. $\Pr[X=x\mid H=h]\ge\alpha$;
--   3. $x\in C$ and $h(x)=0$
--
--   is at most $2(1-p)^s$:
--
--   $$
--   \sum_h\Pr[H=h]\sum_{x:\ (h,x)\ \text{satisfies 1–3}}\Pr[X=x\mid H=h]\le 2\,(1-p)^s .
--   $$
--
--   A low-entropy adversary must therefore query most symbols of its likely answers heavily; otherwise the oracle values it never looked at would make those answers incorrect.
--
--   **Formalization Note** The statement holds for every code $C\subseteq\Sigma^n$ over every finite alphabet; conditions 1–3 are `Event3`. The law of $H$ is the published product weight `ErasureQTanner.noisyWeight p` ($h(u)=1$ with probability $p$), and the expectation over $H$ is `ErasureQTanner.noisyExp`. Outputs are `Option (Σ^n)`, and $X=x$ is the outcome `some x`.
--
--   Differences from the source:
--   - generalization: C the code of §5.2 (Construction 6.2) → any code C ⊆ Σ^n over any finite alphabet Σ; reason: the proof uses no property of C; C = C_λ gives the paper's statement
--   - encoding: the probability over (H, X) of the pairs (h, x) with conditions 1–3 → ErasureQTanner.noisyExp p (h ↦ Σ_{x : Event3} Pr[X = some x | H = h]), the published p-biased product law; reason: definition of the joint law (§7, p.38)
--   - encoding: s ∈ [n] → 1 ≤ s ≤ n; reason: same set
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 7.3, pp.38–39 (PDF pp.40–41)

import Mathlib
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_CertRandQROM_Event3

namespace CertRandQROM

open Classical in
/-- **Lemma 7.3** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), pp.38–39): let
`α ∈ (0, 1]`, `p ∈ (0, 1)` and `s ∈ [n]`, and let `H` be a `p`-biased oracle on `[n] × Σ`. Over
the randomness of `(H, X)` (`H` from the `p`-biased law, then `X ← A^H`), the probability of a
pair `(h, x)` satisfying the three conditions of `Event3` (some `I ⊆ [n]`, `|I| = s`, with
`w̃_{i,x_i}(h) < α/(4n)` on `I`; `Pr[X = x | H = h] ≥ α`; `x ∈ C` and `h(x) = 0`) is at most
`2 (1 − p)^s`:
`Σ_h Pr[H = h] Σ_{x : Event3(h, x)} Pr[X = x | H = h] ≤ 2 (1 − p)^s`.

**Formalization Note** `ErasureQTanner.noisyExp p f = Σ_h Pr[H = h] f(h)` is the expectation under the
published `p`-biased product law (`true` = value `1` with probability `p`). The statement is for every code `C ⊆ Σ^n` and every algorithm with
outputs `Option (Σ^n)`; `X = x` is the outcome `some x`. -/
theorem lemma_7_3_low_entropy_heavy {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S]
    [Fintype W] [DecidableEq W] {Q : ℕ} (C : Finset (Fin n → S))
    (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q) (α p : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hp₀ : 0 < p) (hp₁ : p < 1) (s : ℕ) (hs₁ : 1 ≤ s) (hsn : s ≤ n) :
    ErasureQTanner.noisyExp p
        (fun h => ∑ x : Fin n → S, if Event3 C A α s h x then outProb A h (some x) else 0) ≤
      2 * (1 - p) ^ s := by sorry

end CertRandQROM
