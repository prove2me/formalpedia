-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_tie_core
-- name    : Formalism.CountingSumsFrames.TO.tie_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:21.561768+00:00
-- url     : https://prove2.me/theorems/565a4392-1248-40e0-835a-66cc7e3d8b84
-- title:
--   TO: tie core
-- statement:
--   The TO construction uses the tie core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3104-L3286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L3104-L3286

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.tie_core [NeZero r] (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t) (ρ : Fin r) (e1 : ℕ)
    (hK : T.pos i + 1 + 1 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1) (E : ℝ) (hE : 0 ≤ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h' h'' : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h' x))
    (hhC : ∀ x, h' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hli : LinearIndependent ℚ_[p] h')
    (hspZ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range h'))
    (hh2 : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h'' x))
    (hh2C : ∀ x, h'' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hh2i : ∀ x, h'' x ∈ IntPol p (Fin N × Fin r))
    (d : ι → ℚ_[p]) (cst : ℚ_[p])
    (hdiag : ∀ x y, la x = la y → cst * fock p (T.phi p L i (h' x)) (h'' y) = if x = y then d x else 0)
    (hG0 : ∀ x y, ‖cst * fock p (h' x) (h' y)‖ ≤ 1)
    (vv : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (hvv : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (vv x))
    (hvvC : ∀ x, vv x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr) (hvv0 : ∀ x, vv x ≠ 0) :
    ∃ Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ y ∈ Y p (r := r) L T.J T.thr, Tm y ∈ Y p (r := r) L T.J T.thr) ∧
      (∀ y ∈ YZ p (r := r) L T.J T.thr,
        ((p : ℚ_[p]) ^ (e1 * (T.pos i + 1 + 1) + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
      (∀ u ∈ Y p (r := r) L T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) L T.J T.thr,
        fockN p L (T.phi p L i u) (Tm u') = (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p L (πm u) u') ∧
      (∀ j : Fin T.t, i < j → ∀ u, πm (T.phi p L j u) = T.phi p L j (πm u)) ∧
      Module.finrank ℚ_[p] (Y p (r := r) L T.J T.thr) -
        Module.finrank ℚ_[p] ((Y p (r := r) L T.J T.thr ⊓ LinearMap.ker (πm - LinearMap.id) :
          Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
        ∑ x ∈ univ.filter (fun x => ‖d x‖ < (p : ℝ) ^ (-E)),
          Module.finrank ℚ_[p] (YYs L (T.pos i + 1 + 1) T.J T.thr (vv x)) := by sorry
