-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated
-- name    : AlgebraicCurve.SemistableModel.exists_opens_preimage_eq_of_isClosedMap_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a5bec2c6-72c0-52d9-bced-0955450dafbc
-- title:
--   Descent of saturated open covers along a closed surjection
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and let $\mathrm{Fbar}_i$ ($i \in \iota_V$) be field extensions of the residue field of $A$. Fix component charts $C_i$ for $F$ with residue field $\mathrm{Fbar}_i$, annuli $\mathrm{An}_e$ ($e \in \iota_E$), source and target maps $\mathrm{src}, \mathrm{tgt} : \iota_E \to \iota_V$, marked places $x_s(e)$, $x_t(e)$ on the source and target components, and let $M$ be a semistable model for these data: an integral scheme $M.X$, proper, flat and locally of finite presentation over $\operatorname{Spec} A$, with an identification of $F$ with the function field of $M.X$, together with the points $M.\mathrm{pt}(P)$ attached to places $P$ of $F/L$ (these lie over the generic point of $\operatorname{Spec} A$), the generic points $M.\mathrm{gen}(i)$ of the components, the smooth special points and the nodes. Let $X_1$ be a scheme and $\pi : M.X \to X_1$ a morphism of schemes whose underlying map of topological spaces is closed and surjective, and whose fibres are controlled as follows: any point with the same image as a point lying over the closed point of $\operatorname{Spec} A$ equals that point; any point with the same image as the generic point of $M.X$ is that generic point; and any point with the same image as some $M.\mathrm{pt}(P)$ is of the form $M.\mathrm{pt}(P')$ for some place $P'$ of $F/L$. Let $G : \{\text{places of } F/L\} \to \mathbb{Z}$, let $r \in \mathbb{N}$, let $U_a$ ($a \in \mathrm{Fin}\ r$) be open subsets of $M.X$ with $\bigsqcup_a U_a = \top$, and let $h_a \in F$. Assume that for each $a$ the trace of $U_a$ on the points $M.\mathrm{pt}(P)$ has one of three shapes: either $M.\mathrm{pt}(P) \in U_a \iff G(P) = 0$; or there are $i \in \iota_V$ and a place $q$ of $\mathrm{Fbar}_i$ over the residue field of $A$ with $M.\mathrm{pt}(P) \in U_a \iff \bigl(P \in C_i.\mathrm{dom}$ and $C_i.\mathrm{placeMap}(P) = q\bigr)$ or $\bigl(G(P) = 0$ and $\operatorname{ord}_P(h_a) = 0\bigr)$; or there is $e_0 \in \iota_E$ with $M.\mathrm{pt}(P) \in U_a \iff P \in \mathrm{An}_{e_0}.\mathrm{dom}$ or $\bigl(G(P) = 0$ and $\operatorname{ord}_P(h_a) = 0\bigr)$, where $\operatorname{ord}_P$ is the normalised valuation attached to $P$. Assume finally that both conditions $G(P) = 0$ and $\operatorname{ord}_P(h_a) = 0$ are invariant along the fibres of $\pi$ through the points $M.\mathrm{pt}(P)$, that is, $\pi(M.\mathrm{pt}(P)) = \pi(M.\mathrm{pt}(P'))$ implies $G(P) = 0 \iff G(P') = 0$ and, for each $a$, $\operatorname{ord}_P(h_a) = 0 \iff \operatorname{ord}_{P'}(h_a) = 0$. Then there are open subsets $U_a^1$ of $X_1$ ($a \in \mathrm{Fin}\ r$) with $\bigsqcup_a U_a^1 = \top$ and $U_a = \pi^{-1}(U_a^1)$ for every $a$, in the pointwise form: $x \in U_a \iff \pi(x) \in U_a^1$ for all $x \in M.X$.
--
--   This is the topological descent step for open covers along the closed surjective map $\pi$: a closed surjection is a quotient map, so an open set saturated for $\pi$ is the preimage of an open set, and the hypotheses on the fibres and on the three admissible shapes of the traces $U_a$ guarantee saturation. It is used to transfer a cover adapted to Cartier data from a semistable model over the valuation ring $A$ to a scheme at a finite level, and is cited by the two results producing Cartier data for Kummer covers at finite level from Cartier data on a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.exists_opens_preimage_eq_of_isClosedMap_of_saturated
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (X₁ : Scheme.{u}) (π : M.X ⟶ X₁)
    (hcl : IsClosedMap π.base) (hsurj : Function.Surjective π.base)
    (hfib_sp : ∀ x x' : M.X, π.base x' = π.base x → M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x)
    (hfib_gen : ∀ x' : M.X, π.base x' = π.base (genericPoint M.X) → x' = genericPoint M.X)
    (hfib_pt : ∀ (P : Place L F) (x' : M.X), π.base x' = π.base (M.pt P) → ∃ P' : Place L F, x' = M.pt P')
    (G : Place L F → ℤ)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hU : (⨆ a, U a) = ⊤)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔ G P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨ (G P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨ (G P = 0 ∧ P.ord (h a) = 0))))
    (hGfib : ∀ P P' : Place L F, π.base (M.pt P) = π.base (M.pt P') → (G P = 0 ↔ G P' = 0))
    (hhfib : ∀ a (P P' : Place L F), π.base (M.pt P) = π.base (M.pt P') →
      (P.ord (h a) = 0 ↔ P'.ord (h a) = 0)) :
    ∃ U₁ : Fin r → X₁.Opens, (⨆ a, U₁ a) = ⊤ ∧ ∀ a (x : M.X), x ∈ U a ↔ π.base x ∈ U₁ a := by sorry
