-- Prove2me | Theorems.Thm_CTB_kernel_normal
-- name    : CTB.kernel_normal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:24.929983+00:00
-- url     : https://prove2.me/theorems/f35684a5-5eea-4b33-9ba6-1b314e5b70ac
-- title:
--   The kernel of a realization is normal in the total-space subgroup (Proposition 2.1 and Lemma 2.2)
-- statement:
--   The kernel of a torus-bundle realization is normal in the total-space subgroup. If the pair of subgroups with the homomorphism realizes the abstract model group, and the total-space subgroup is torsion-free, then the kernel is stable under conjugation by the elements of the total-space subgroup, so the quotient is a group and the realization fits into the short exact sequence of the fibration. This is the idealized form of the normality step shared by Proposition 2.1 and Lemma 2.2 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 2 (Proposition 2.1, with Lemma 2.2).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 2 (Proposition 2.1 and Lemma 2.2, idealized): the kernel
of a torus-bundle realization is normal in the total-space subgroup.
If the pair of subgroups with the homomorphism f realizes the abstract
model group, and the total-space subgroup is torsion-free, then the
kernel is stable under conjugation by the elements of the total-space
subgroup, so that the quotient is a group and the realization fits into
the short exact sequence of the fibration. -/
theorem kernel_normal {n : ℕ} {Q : Type*} [Group Q] {G : Type*} [Group G]
    (W : CrystallographicBraidWorld n Q)
    (Gam Ker : Subgroup Q) (f : Q →* G)
    (h : IsTorusBundleRealization W Gam Ker f) (hT : TorsionFree ↥Gam) :
    ∀ g ∈ Gam, ∀ k ∈ Ker, g * k * g⁻¹ ∈ Ker := by sorry

end CTB
