-- Prove2me | Theorems.Thm_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units
-- name    : ExtCitation.extVanishingCts_of_e2ClassGroup_and_e2Units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/39ed4c74-e39b-5339-8073-b82c2ed0bc9d
-- title:
--   Kummer reduction of continuous (EXT) vanishing for p ≥ 5
-- statement:
--   Let $p$ be a prime with $5 \le p$, and write $K =$ `CyclotomicField p ℚ` with ring of integers $\mathcal{O}_K$. Two Galois actions are in play. First, `clGalAction p K` is the action of $(\mathbb{Z}/p)^\times$ on `ClGalModule p (𝓞 K)`, the quotient of the additive group underlying $\mathrm{Cl}(\mathcal{O}_K)$ by its $p$-th multiples, obtained from the ring automorphisms `clRingAction p K d` of $\mathcal{O}_K$ attached to $d \in (\mathbb{Z}/p)^\times$ through the isomorphism `cycloGalEquiv`. Second, a monoid homomorphism `unitsGalAction'` from $(\mathbb{Z}/p)^\times$ to the $\mathbb{Z}/p$-linear endomorphisms of $\mathcal{O}_K^\times / (\mathcal{O}_K^\times)^p$ is given as data, assumed (hypothesis `hρ`) to send the class of a unit $u$ to the class of the image of $u$ under `clRingAction p K d`. The hypotheses are: (`hE2CL`) every $a$ in the mod $p$ class group with `clGalAction p K d a = (d : ZMod p)^2 • a` for all $d$ vanishes; and (`hUnitsB2`) every unit $u$ of $\mathcal{O}_K$ whose class satisfies the same $\omega^2$-eigenvector condition for `unitsGalAction'`, and which is a $p$-th power in the units of the $\mathfrak{p}$-adic completion of $K$ for every height-one prime $\mathfrak{p}$ of $\mathcal{O}_K$ containing $p$, has trivial class in $\mathcal{O}_K^\times / (\mathcal{O}_K^\times)^p$. The conclusion is `ExtVanishingCts p`: for every $\mathbb{Z}/p$-vector space $V$ carrying an action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ commuting with the scalars, and every $\mathbb{Z}/p$-submodule $C \subseteq V$ satisfying the predicate `IsAdmissibleExtension p V C` together with the further requirement that the set of $\sigma$ fixing $V$ pointwise is open, there exists a Galois-stable $\mathbb{Z}/p$-submodule $C'$ of $V$ complementary to $C$.
--
--   This is the Kummer-theoretic reduction of the splitting statement for continuous admissible extensions to the two arithmetic inputs for $\mathbb{Q}(\zeta_p)$ at the $\omega^2$-eigenspace: the vanishing of the $\omega^2$-part of the mod $p$ class group, and the statement that $\omega^2$-eigen-units which are local $p$-th powers above $p$ are global $p$-th powers. It is used by [`ExtCitation.extVanishingCts_of_five_le`](thm.html#ExtCitation.extVanishingCts_of_five_le), where the two inputs are supplied, in the line of argument that produces the vanishing hypothesis (EXT) for $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.lean

import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_ExtCitation_CyclotomicUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace ExtCitation
open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]

theorem extVanishingCts_of_e2ClassGroup_and_e2Units (hp5 : 5 ≤ p)
    (unitsGalAction' : (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)))
    (hρ : ∀ d u, unitsGalAction' d
        (ModP.proj p _ (Additive.ofMul u)) =
      ModP.proj p _ (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)))
    (hE2CL : ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a → a = 0)
    (hUnitsB2 : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      IsOmegaEigenvector unitsGalAction' 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
        (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
        ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
          v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
            (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) →
      ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0) :
    ExtVanishingCts p := by sorry
