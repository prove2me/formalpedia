-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_tensorSat
-- name    : Formalism.GM.M.SSD.tensorSat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:33.261622+00:00
-- url     : https://prove2.me/theorems/fb6a36c1-8896-4d13-8eca-64f777ee69ce
-- title:
--   SSD: tensor Sat
-- statement:
--   The SSD construction uses the tensor Sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L363-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L363-L410

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ τ : Type} [DecidableEq σ] (e : τ → σ)

theorem Formalism.GM.M.SSD.tensorSat (he : Function.Injective e) (Yq : Submodule ℚ_[p] (MvPolynomial τ ℚ_[p])) (YZs : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (hYZ : ∀ y ∈ YZs, y ∈ Yq) (hYZ' : ∀ y ∈ Yq, IsInt y → y ∈ YZs)
    (G : Set (MvPolynomial σ ℚ_[p])) (Mb : Finset (σ →₀ ℕ))
    (hG1 : ∀ g ∈ G, g.support ⊆ Mb) (hG2 : ∀ μ ∈ Mb, monomial μ 1 ∈ G) (hG3 : ∀ μ ∈ Mb, ∀ x, μ (e x) = 0)
    (zm : σ →₀ ℕ) (Q : MvPolynomial σ ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g})
    (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g} := by sorry
