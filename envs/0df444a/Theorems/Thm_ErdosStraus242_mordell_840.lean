-- Prove2me | Theorems.Thm_ErdosStraus242_mordell_840
-- name    : ErdosStraus242.mordell_840
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:43:27.580286+00:00
-- url     : https://prove2.me/theorems/185c5245-9a80-40de-86ff-e3e051224df9
-- title:
--   Mordell–Yamamoto six-class congruence reduction
-- statement:
--   For every prime natural number $p>2$, if the remainder $p\bmod840$ is outside $\{1,121,169,289,361,529\}$, then there exist natural numbers $1≤ x<y<z$ with $4/p=1/x+1/y+1/z$ in the rationals. This is a known congruence result to formalize, not an assumed covering theorem. The exact distinct-denominator adaptation remains part of the Lean proof obligation.
-- source:
--   Yamamoto (1965), §§3–4, pp. 42–46, especially the printed list on p. 46, https://www.jstage.jst.go.jp/article/kyushumfs/19/1/19_1_37/_pdf/-char/en; Mordell, Diophantine Equations (1969), ch. 30 pp. 287–290 (bibliographic reference; relevant full chapter not accessible); current authoritative list https://www.erdosproblems.com/242. Historical positive-denominator formulations are adapted here to strict ordering. Bloom–Elsholtz p. 239 prints a discrepant 49/529 list and is not used for this set.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem mordell_840 (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∉ ({1, 121, 169, 289, 361, 529} : Finset ℕ)) :
    IsErdosStraus p := by sorry
end ErdosStraus242
