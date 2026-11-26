-- Prove2me | Theorems.Thm_Eden_antitone_eq_of_multiset_eq
-- name    : Eden.antitone_eq_of_multiset_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:33.170283+00:00
-- url     : https://prove2.me/theorems/8e851c78-fbc8-51c5-afdf-5615a11d03e3
-- title:
--   Eden: antitone eq of multiset eq
-- statement:
--   The Eden construction uses the antitone eq of multiset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L17-L22
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L17-L22

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.antitone_eq_of_multiset_eq {n : ℕ} {a b : Fin n → ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) : a = b := by sorry
