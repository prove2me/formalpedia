-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_ofNbr_adjoint
-- name    : Formalism.L2.Col.LocOp.ofNbr_adjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:41.33128+00:00
-- url     : https://prove2.me/theorems/4dbb9727-c89e-4f4c-903e-b2522dece2e5
-- title:
--   Loc Op: of Nbr adjoint
-- statement:
--   The Loc Op construction uses the of Nbr adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L606-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L606-L644

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}

theorem Formalism.L2.Col.LocOp.ofNbr_adjoint (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (nb : S'.D → Finset S.D) (nb' : S.D → Finset S'.D) (T : S.V →ₗ[K] S'.V) (T' : S'.V →ₗ[K] S.V)
    (hn : ∀ g d' d, (e.symm : S'.G →* S.G) g • d ∈ nb (g • d') ↔ d ∈ nb d')
    (hT : ∀ g x, T (S.ρ ((e.symm : S'.G →* S.G) g) x) = S'.ρ g (T x))
    (hn' : ∀ g d d', (e : S.G →* S'.G) g • d' ∈ nb' (g • d) ↔ d' ∈ nb' d)
    (hT' : ∀ g x, T' (S'.ρ ((e : S.G →* S'.G) g) x) = S.ρ g (T' x))
    (htr : ∀ d d', d ∈ nb d' ↔ d' ∈ nb' d) (h0 : T = 0 ↔ T' = 0)
    (hadj : ∀ x y, S'.pair (T x) y = S.pair x (T' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' ((ofNbr (e.symm : S'.G →* S.G) nb T hn hT).op φ) ψ =
      S.ipOf h s φ ((ofNbr (e : S.G →* S'.G) nb' T' hn' hT').op ψ) := by sorry
