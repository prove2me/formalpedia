-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_forall_rigidified
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_forall_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1885d87f-6ee3-5fa1-b307-809e63634643
-- title:
--   Removing the rigidification hypothesis in Zariski gluing
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$ and a commutative ring $S$ in which the image of $n$ is a unit. Here a `PolarisedAbelianScheme g d n` over a ring consists of a scheme $A$ with a morphism $f$ to the spectrum of that ring together with a commutative relative group law on $f$, the property bundle (smooth, proper, connected fibres, group law present), all fibres of topological Krull dimension $g$, sections $P_1,\dots,P_{2g}$ over the identity killed by $n$ whose $\{0,\dots,n-1\}$-combinations are pairwise distinct and exhaust the $n$-torsion on every geometrically algebraically closed fibre, and an invertible module `pol` on $A$ whose sections give a closed immersion into a projective space over the base and whose $H^0$ on every geometric fibre has dimension $d$; `IsPullback φ u u'` asserts the existence of a morphism $u'.A \to u.A$ forming a pullback square over $\mathrm{Spec}\,φ$, compatible with the group laws, carrying the marked sections to the base changes of the marked sections, and pulling `pol` back to `pol'`; `Iso` asserts an isomorphism of the schemes over the base compatible with the group laws, matching the marked sections, and matching the polarisations locally on the base. The hypothesis $H$ is the rigidified gluing statement for every basic-open cover datum: for every $k'$, every $r' : \mathrm{Fin}\,k' \to S$ whose range generates the unit ideal, and every family of $S$-algebras $B'_i$ with $B'_i$ a localisation of $S$ away from $r'_i$, every family $u_i$ of such polarised abelian schemes over the $B'_i$ for which each pullback of $u_i$'s polarisation along the unit section of its group law is isomorphic to the unit sheaf of modules, and which is compatible on overlaps in the sense that for all $i,j$, every $S$-algebra $C$ that is a localisation of $S$ away from $r'_i r'_j$, all $S$-algebra maps $B'_i \to C$, $B'_j \to C$ and all objects $v_1, v_2$ over $C$ that are pullbacks of $u_i$, $u_j$ along these maps, one has $v_1 \cong v_2$, admits $u_0$ over $S$ such that every pullback of $u_0$ to $B'_i$ along the structural map is isomorphic to $u_i$. The conclusion is the same gluing statement for the given cover $r : \mathrm{Fin}\,k \to S$ with range generating the unit ideal and the given family $B_i$ of localisations of $S$ away from $r_i$, but with no triviality condition imposed on the polarisations: for every family $u_i$ over the $B_i$ satisfying the overlap condition above, there is $u_0$ over $S$ all of whose pullbacks to the $B_i$ are isomorphic to the corresponding $u_i$.
--
--   This is the descent step that removes the auxiliary rigidification (triviality of the polarisation along the zero section) from the Zariski gluing of polarised abelian schemes with full level-$n$ structure, by passing to a refinement of the given basic-open cover on which the pullbacks along the unit sections become trivial. It feeds directly into the unconditional gluing statement [`AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le), part of the construction of moduli of polarised abelian schemes with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_forall_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_forall_rigidified
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (H : ∀ {k' : ℕ} (r' : Fin k' → S) (_ : Ideal.span (Set.range r') = ⊤)
      (B' : Fin k' → Type) [∀ i, CommRing (B' i)] [∀ i, Algebra S (B' i)] [∀ i, IsLocalization.Away (r' i) (B' i)],
      (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B' i)),
        (∀ i, Nonempty ((Scheme.Modules.pullback ((u i).L.one (𝟙 (Spec (CommRingCat.of (B' i))))).1).obj (u i).pol ≅
            SheafOfModules.unit (Spec (CommRingCat.of (B' i))).ringCatSheaf)) →
        (∀ (i j : Fin k') (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r' i * r' j) C]
            (ρ₁ : B' i →ₐ[S] C) (ρ₂ : B' j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
            PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
            PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
            PolarisedAbelianScheme.Iso v₁ v₂) →
        ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k') (v : PolarisedAbelianScheme g d n (B' i)),
          PolarisedAbelianScheme.IsPullback (algebraMap S (B' i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)] :
    (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B i)),
      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
          (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
          PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
          PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
          PolarisedAbelianScheme.Iso v₁ v₂) →
      ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k) (v : PolarisedAbelianScheme g d n (B i)),
        PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) := by sorry
