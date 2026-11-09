-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_lemma_2_2
-- name    : CKKSPrecision.FourierUnits.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:40:39.703716+00:00
-- url     : https://prove2.me/theorems/d5b49bb3-ad4b-441b-941e-c42985ee2dbb
-- title:
--   Lemma 2.2 — exact logarithmic lattice index
-- statement:
--   Let $m>2$ be a prime power, and select one embedding from each conjugate pair using a representative set $S$ as above. Let $\Lambda=\operatorname{Log}(R^\times)$ and let $h^+(m)$ be the ordinary ideal class number of $\mathbb Q(\zeta+\zeta^{-1})$. Then
--   $$
--   [\Lambda:\operatorname{Log}(C_m)]=h^+(m).
--   $$
--   The equality gives the exact finite index, rather than only finite-index inclusion. It connects the cyclotomic generators to the full real span of the integral unit lattice.
--
--   Differences from the source:
--   - encoding: $K=\mathbb Q(\zeta)$ with the specified primitive complex root → Mathlib splitting field with the distinguished root sent to $\exp(2\pi i/m)$ by a fixed embedding; reason: an isomorphic model of the same field and root, with no additional hypothesis
--   - encoding: additive logarithmic lattices and their exact index → image subgroups of the multiplicative type synonym of the real coordinate space, with `relIndex` equal to the ordinary class number; reason: the type synonym changes notation only; infinite relative index is encoded by zero, while the class number is positive, so the equality enforces finite index
--   - encoding: one representative of each conjugate pair of embeddings → one least positive residue representative from each invertible sign pair, in a finite set containing $1$; reason: this is the source quotient indexing, with no restriction on the number field or its units
--   - encoding: a prime-power integer conductor $m>2$ → a positive natural conductor with the same strict inequality and `IsPrimePow` predicate; reason: positivity is already implied by the source inequality, and the predicate is the usual prime-power property
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 5, Lemma 2.2, citing [CDPR16, Theorem 2.8] (PDF p. 7)

import Definitions.Def_CKKSPrecision_FourierUnits_arithmetic_model

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits

theorem lemma_2_2 (m : ℕ+) (hm : 2 < (m : ℕ)) (hp : IsPrimePow (m : ℕ))
    (S : Finset ℕ) (hS : IsRepresentatives m S) :
    (circularLattice m S).relIndex (unitLattice m S) = realClassNumber m := by sorry

end CKKSPrecision.FourierUnits
