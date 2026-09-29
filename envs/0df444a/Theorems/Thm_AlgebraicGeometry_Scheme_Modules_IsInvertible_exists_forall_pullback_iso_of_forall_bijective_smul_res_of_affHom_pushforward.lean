-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/12b143db-d8e9-5d28-a282-d8c6f7522736
-- title:
--   Gluing a line bundle from an affine datum over adic thickenings
-- statement:
--   Let $R$ be a commutative ring, $I \subseteq R$ an ideal, and $f : X \to \operatorname{Spec} R$ a separated morphism of schemes. For each $n$, `adicThickening f I n` is the fibre product of $f$ with $\operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, and `adicThickeningι f I n` is its canonical morphism to $X$. Suppose given, for every $n$, a module $L_n$ on this thickening together with a proof that $L_n$ is invertible, i.e. every point of the thickening lies in an open $U$ on which the pullback of $L_n$ along $U.\iota$ is isomorphic to the unit module. Let $G$ be an `OModulePresheaf` for $f$: a datum assigning to each open $U \subseteq X$ an abelian group with compatible $R$- and $\Gamma(X,U)$-module structures and $R$-linear restriction maps satisfying the usual semilinearity, identity and composition identities, with no sheaf condition imposed. Suppose given for each $n$ an `AffHom` $\psi_n$ from $G$ to the pushforward along `adicThickeningι f I n` of the sections datum of $L_n$ — that is, $R$-linear maps $G(U) \to \Gamma(L_n, \iota_n^{-1}U)$ for $U$ affine open in $X$, satisfying $\psi_n(a \cdot x) = a \cdot \psi_n(x)$ for $a \in \Gamma(X,U)$ and commuting with restriction between affine opens — and assume each $\psi_n$ is surjective on every affine open. Finally assume a family $U : \kappa \to X.\text{affineOpens}$ with $\bigsqcup_i U_i = \top$, sections $g_i \in G(U_i)$, such that for every $i$ and every affine open $V \le U_i$ the map $b \mapsto b \cdot (g_i|_V)$ from $\Gamma(X,V)$ to $G(V)$ is bijective. The conclusion: there exists a module $M$ on $X$ which is invertible and whose pullback along `adicThickeningι f I n` is isomorphic to $L_n$ for every $n$.
--
--   This is the gluing step in a formal-existence argument: a rank-one-free module datum on an affine cover of a separated scheme, mapping onto the direct images of invertible modules on the $I$-adic thickenings of $X$, is realised by a genuine line bundle on $X$ inducing all of them. It is used in the deduction of the corresponding statement under the hypothesis that the kernels of the thickening maps are given by powers of $I$, part of the construction of line bundles and Picard-functor data for relative curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (G : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom G
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    {κ : Type u} (U : κ → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (g : ∀ i, G.obj (U i).1)
    (hg : ∀ (i : κ) (V : X.affineOpens) (hV : V.1 ≤ (U i).1),
      Function.Bijective fun b : Γ(X, V.1) => b • G.res hV (g i)) :
    ∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧
      ∀ n, Nonempty ((Scheme.Modules.pullback (adicThickeningι f I n)).obj M ≅ L n) := by sorry
