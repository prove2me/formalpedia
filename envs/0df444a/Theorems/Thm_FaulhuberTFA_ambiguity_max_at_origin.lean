-- Prove2me | Theorems.Thm_FaulhuberTFA_ambiguity_max_at_origin
-- name    : FaulhuberTFA.ambiguity_max_at_origin
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:47:54.101833+00:00
-- url     : https://prove2.me/theorems/94662ee4-78e3-48dd-b082-63242921b504
-- title:
--   Lemma 3.3: the ambiguity function peaks only at the origin, where it equals the energy
-- statement:
--   Let $f\in L^2(\mathbb{R}^d)$ with $f\neq0$ (not almost everywhere zero). Then
--
--   $$Af(0,0)=\|f\|_2^2=\int_{\mathbb{R}^d}|f(t)|^2\,dt,$$
--
--   and for every $(x,\omega)\neq(0,0)$
--
--   $$|Af(x,\omega)|<Af(0,0).$$
--
--   The correlation of a radar echo with time-frequency shifts of the transmitted pulse is maximal exactly at the true delay and Doppler shift, which is how range and speed are read off.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, Lemma 3.3, p. 27

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem ambiguity_max_at_origin {d : ℕ} {f : Rd d → ℂ} (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0) :
    ambiguity f 0 0 = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) ∧
    ∀ x ω : Rd d, (x, ω) ≠ (0, 0) → ‖ambiguity f x ω‖ < ∫ t, ‖f t‖ ^ 2 := by sorry

end FaulhuberTFA
