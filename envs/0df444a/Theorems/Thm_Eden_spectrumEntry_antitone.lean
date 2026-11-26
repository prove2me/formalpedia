-- Prove2me | Theorems.Thm_Eden_spectrumEntry_antitone
-- name    : Eden.spectrumEntry_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:08.708343+00:00
-- url     : https://prove2.me/theorems/4eb45129-ae09-4d11-8ad6-a7fea2d01824
-- title:
--   Eden: spectrum Entry antitone
-- statement:
--   The Eden construction uses the spectrum Entry antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L15-L19
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L15-L19

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumEntry_antitone {a : Fin 5 → ℝ} (ha : Antitone a)
    {i j : ℕ} (hij : i ≤ j) (hj : j < 5) : spectrumEntry a j ≤ spectrumEntry a i := by sorry
