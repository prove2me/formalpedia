-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_of_index_between
-- name    : Eden.kaplanYorkeDimension_of_index_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:58.312982+00:00
-- url     : https://prove2.me/theorems/ef8a973e-3464-52b4-93f5-20a00b2b7a55
-- title:
--   Eden: kaplan Yorke Dimension of index between
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension of index between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L101-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L101-L104

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_of_index_between {a : Fin 5 → ℝ} {j : ℕ}
    (hj : kaplanYorkeIndex a = j) (hj₀ : 0 < j) (hj₅ : j < 5) :
    kaplanYorkeDimension a = (j : ℝ) + spectrumPartialSum a j / |spectrumEntry a j| := by sorry
