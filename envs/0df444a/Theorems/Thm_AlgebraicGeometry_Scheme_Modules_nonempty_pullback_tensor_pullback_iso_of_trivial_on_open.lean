-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/ea2be51d-7ee0-5fd2-95db-ff2307a9677c
-- title:
--   Tensoring by a pullback trivial on V is invisible over q⁻¹V
-- statement:
--   Let $Y$ and $T$ be schemes (in a fixed universe), let $q \colon Y \to T$ be a morphism of schemes, let $V$ be an open subscheme of $T$, let $L$ be a sheaf of $\mathcal O_Y$-modules and let $N$ be a sheaf of $\mathcal O_T$-modules. Restriction to an open is spelled throughout as inverse image along the canonical open immersion: `Scheme.Modules.pullback V.ι` for $V \hookrightarrow T$, and `Scheme.Modules.pullback (q ⁻¹ᵁ V).ι` for the open immersion of the scheme-theoretic preimage $q^{-1}V \hookrightarrow Y$. Assume given an isomorphism $eN$ of sheaves of $\mathcal O_V$-modules between the inverse image of $N$ along $V \hookrightarrow T$ and the monoidal unit of the category of sheaves of modules on $V$, i.e. a trivialisation $N|_V \cong \mathcal O_V$. The conclusion asserts that the type of isomorphisms of sheaves of $\mathcal O_{q^{-1}V}$-modules between the restriction to $q^{-1}V$ of $L \otimes q^{*}N$ and the restriction to $q^{-1}V$ of $L$ is nonempty; thus an isomorphism $(L \otimes q^{*}N)|_{q^{-1}V} \cong L|_{q^{-1}V}$ exists, no particular one being named by the statement.
--
--   This is the standard fact that twisting a module by the pullback of a module that is trivial over an open $V \subseteq T$ changes nothing over the preimage $q^{-1}V$. It is used in the study of relative line bundles and relative effective Cartier divisors, being cited by [`AlgebraicGeometry.RelEffCartierDiv.supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn`](thm.html#AlgebraicGeometry.RelEffCartierDiv.supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn), [`AlgebraicGeometry.RelPicard.relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre) and [`AlgebraicGeometry.RelPicard.relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn`](thm.html#AlgebraicGeometry.RelPicard.relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
    {Y T : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) (L : Y.Modules) (N : T.Modules)
    (eN : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : AlgebraicGeometry.Scheme.{u}).Modules)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj
        (L ⊗ (AlgebraicGeometry.Scheme.Modules.pullback q).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj L) := by sorry
