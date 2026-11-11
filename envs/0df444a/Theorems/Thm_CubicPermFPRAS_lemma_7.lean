-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_7
-- name    : CubicPermFPRAS.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:01.303499+00:00
-- url     : https://prove2.me/theorems/ebd557aa-fea6-4708-b7d9-bd3f2f2f5c2b
-- title:
--   Lemma 7, p.9 — cooling schedule $1=\lambda_0>\dots>\lambda_L=e^{-\lceil\log_2 n!\rceil}$, $L=O(n\log^2n)$, ratios in $[3/4,4/3]$, $\mathbb E[Y^2]/\mathbb E[Y]^2\le64/27$
-- statement:
--   Let $A$ be an $n\times n$ 0/1 matrix whose bipartite graph $G$ has a perfect matching, and let $\lambda_i=e^{-\beta_i}$ be the cooling schedule (Lemma 50 with $H(M)=|M\setminus E|$, $H_{\max}=n$, $\beta_{\max}=\lceil\log_2 n!\rceil$, $\Delta=2\beta_{\max}$). There is a universal constant $C$ such that
--   $$1=\lambda_0>\lambda_1>\dots>\lambda_L=\exp(-\lceil\log_2 n!\rceil)\le\frac1{n!},\qquad L\le Cn\log^2n,$$
--   for every $0\le i<L$ and every $(u,v)$ the ideal hole weights satisfy $\tfrac34\le w^*_{i+1}(u,v)/w^*_i(u,v)\le\tfrac43$, and for independent $M_i\sim\mu_i$ the product $Y=\prod_{i<L}\lambda_{i+1}(M_i)/\lambda_i(M_i)$ satisfies
--   $$\mathbb E[Y]=\frac{Z_L}{Z_0},\qquad\frac{\mathbb E[Y^2]}{\mathbb E[Y]^2}\le\frac{64}{27}.$$
--
--   The ratio bound keeps accurate weights rough at the next temperature, and the second-moment bound controls the whole-product estimator of Phase 2.
--
--   Differences from the source:
--   - generalization: "there is an explicit schedule" → the algorithm's schedule $\lambda_i=e^{-\beta_i}$ of the proof (p.55); reason: the defined schedule witnesses the existential
--   - encoding: $L=O(n\log^2 n)$; $\mathbb E[Y]$, $\mathbb E[Y^2]$ for independent $M_i$ → a universal $C$; products over $i<L$ of the single-temperature moments; reason: standard reading of $O(\cdot)$; independence factorizes the moments
--   - encoding: an $n\times n$ instance ($V_1$, $V_2$ of size $n$) → the hypothesis $1\le n$; reason: the paper's vertex classes $V_1,V_2$ are nonempty throughout (an anchor $r\in V_1$ exists); $n=0$ is no instance of the source
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 7, p.9 (PDF 11); proof, p.55 (PDF 57)

import Mathlib
import Definitions.Def_CubicPermFPRAS_coolingSchedule

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 7** (cooling schedule), p.9 (PDF 11), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); proved on p.55 (PDF 57).

For an `n × n` 0/1 matrix `A` whose graph has a perfect matching, the explicit schedule
`λ_i = e^{−β_i}` (Lemma 50 with `H(M) = |M \ E|`, `H_max = n`, `β_max = ⌈log₂ n!⌉`, `Δ = 2β_max`)
satisfies `1 = λ₀ > λ₁ > ⋯ > λ_L = exp(−⌈log₂(n!)⌉) ≤ 1/n!`, `L = O(n log² n)`; consecutive
ideal hole weights satisfy `3/4 ≤ w*_{i+1}(u,v)/w*_i(u,v) ≤ 4/3` (8); and for independent
`M_i ∼ µ_i`, `Y = ∏_{i<L} λ_{i+1}(M_i)/λ_i(M_i)` has `E[Y] = Z_L/Z_0` and
`E[Y²]/E[Y]² ≤ 64/27` (9).

**Formalization Note.** The standing assumption of §4 (p.6) that `G` has a perfect matching
`M*` is the hypothesis `HasPM A`. The "explicit schedule" is the algorithm's schedule
`coolLam n`. `E[Y]` and `E[Y²]` are the products over `i < L` of the single-temperature moments
(independence). -/
theorem lemma_7 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      HasPM A →
      coolLam n 0 = 1 ∧
      (∀ i < coolLen n, coolLam n (i + 1) < coolLam n i) ∧
      coolLam n (coolLen n) = Real.exp (-(Nat.clog 2 n.factorial : ℝ)) ∧
      Real.exp (-(Nat.clog 2 n.factorial : ℝ)) ≤ 1 / (n.factorial : ℝ) ∧
      (coolLen n : ℝ) ≤ C * n * Real.log n ^ 2 ∧
      (∀ i < coolLen n, ∀ u v : Fin n,
        3 / 4 ≤ idealHW (tempAct A (coolLam n (i + 1))) u v / idealHW (tempAct A (coolLam n i)) u v ∧
        idealHW (tempAct A (coolLam n (i + 1))) u v / idealHW (tempAct A (coolLam n i)) u v ≤ 4 / 3) ∧
      (∏ i ∈ Finset.range (coolLen n),
          ratioMean (tempAct A (coolLam n i)) (tempAct A (coolLam n (i + 1)))) =
        familyWeight (tempAct A (coolLam n (coolLen n))) (PSet n) /
          familyWeight (tempAct A (coolLam n 0)) (PSet n) ∧
      (∏ i ∈ Finset.range (coolLen n),
          ratioMean2 (tempAct A (coolLam n i)) (tempAct A (coolLam n (i + 1)))) /
        (∏ i ∈ Finset.range (coolLen n),
          ratioMean (tempAct A (coolLam n i)) (tempAct A (coolLam n (i + 1)))) ^ 2 ≤ 64 / 27 := by sorry

end CubicPermFPRAS
