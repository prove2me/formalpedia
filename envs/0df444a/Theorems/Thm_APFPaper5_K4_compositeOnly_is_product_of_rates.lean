-- Prove2me | Theorems.Thm_APFPaper5_K4_compositeOnly_is_product_of_rates
-- name    : APFPaper5.K4.compositeOnly_is_product_of_rates
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:23:40.031342+00:00
-- url     : https://prove2.me/theorems/074ddcd8-c1ba-45c8-84a3-379539eba83a
-- title:
--   Composite Only is product of rates
-- statement:
--   On a model product, compositeOnly reads minus twice the product of the two crossIm values. The compared sum of two books is not an adopted mixture/additivity law. This is not physical local tomography, field selection, or a derivation of rates.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_composite_only_reading.lean', 'sha256': 'fcf4a9f1946d52406cc95920e36573d87c42f381d92af590cb28cada7050a0b5', 'line': 82, 'declaration': 'APFPaper5.K4.compositeOnly_is_product_of_rates'}]

import Definitions.Def_APFPaper5_K4_CompositeOnly
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.compositeOnly_is_product_of_rates (h k : Held2) :
    linearRecord compositeOnly (pair h k) = -2 * crossIm h * crossIm k := by sorry
