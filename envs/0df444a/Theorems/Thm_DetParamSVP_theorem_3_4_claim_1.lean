-- Prove2me | Theorems.Thm_DetParamSVP_theorem_3_4_claim_1
-- name    : DetParamSVP.theorem_3_4_claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:46.155574+00:00
-- url     : https://prove2.me/theorems/39a94d07-ed8a-48ba-91cb-9686741efac4
-- title:
--   Theorem 3.4, Claim 1 — $\lambda_1^{(p)}(\mathcal L_{q,k})>D$
-- statement:
--   Let $p\ge1$, $k\ge2$, let $q>2k$ be prime and let $D$ be a natural number with $D^p<2k$. Then the Reed–Solomon lattice of Eq. (5) satisfies
--
--   $$\lambda_1^{(p)}(\mathcal L_{q,k})>D .$$
--
--   This is condition (i) of Definition 3.1 for the lattice constructed in Theorem 3.4.
--
--   Differences from the source:
--   - encoding: λ₁^{(p)}(L_{q,k}) > D → every nonzero v ∈ L_{q,k} has ‖v‖_p > D; reason: the minimum is attained
--   - generalization: the setting of Theorem 3.4: positive m, d, D, h, k with D ≥ 2, k ≥ 2, d^p ≤ h, D^p < 2k, and q a prime with T < q < 2T → only k ≥ 2, q prime with q > 2k, and D^p < 2k; reason: these are the hypotheses the proof of the claim names; every (q, k, D) of the source satisfies them (T > 2k)
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, Claim 1, p.19

import Definitions.Def_DetParamSVP_LpNorm
import Definitions.Def_DetParamSVP_RSConstruction

set_option autoImplicit false

namespace DetParamSVP

/-- **Claim 1 in the proof of Theorem 3.4.** The lattice `L_{q,k}` satisfies
`λ₁^{(p)}(L_{q,k}) > D`. (Its proof uses `k ≥ 2`, `q > 2k` and `D^p < 2k`.)

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.4, Claim 1, p.19.

**Formalization Note.** `λ₁ > D` is "every nonzero `v ∈ L_{q,k}` has `‖v‖_p > D`". The hypotheses
are the ones the proof of the claim names; the other standing hypotheses of Theorem 3.4 are
dropped. -/
theorem theorem_3_4_claim_1 (p : ℝ) (hp : 1 ≤ p) (q k D : ℕ) [Fact q.Prime] (hk : 2 ≤ k)
    (hqk : 2 * k < q) (hDk : (D : ℝ) ^ p < 2 * k) :
    ∀ v ∈ rsLattice q k, v ≠ 0 → (D : ℝ) < lpNorm p v := by sorry

end DetParamSVP
