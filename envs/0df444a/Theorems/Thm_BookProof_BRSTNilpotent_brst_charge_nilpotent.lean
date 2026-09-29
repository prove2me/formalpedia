-- Prove2me | Theorems.Thm_BookProof_BRSTNilpotent_brst_charge_nilpotent
-- name    : BookProof.BRSTNilpotent.brst_charge_nilpotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:06:46.52392+00:00
-- url     : https://prove2.me/theorems/3cfd1258-01ef-4fdb-aae6-5f2c83d99e00
-- title:
--   The BRST charge is nilpotent
-- statement:
--   The BRST charge is nilpotent.
--
--   Let $f_{abe}$ be structure constants satisfying the Jacobi identity and $\chi,\beta$ ghost creation/annihilation operators with canonical anticommutation relations. The cubic BRST charge
--   $$
--   Q=\sum_{a,b,e} f_{abe}\,\chi_a\chi_b\,\beta_e
--   $$
--   squares to zero: $Q^2=0$. The quartic term vanishes by antisymmetry, the contracted terms vanish by the Jacobi identity, and the surviving cubic remainder cancels against the corresponding one-contraction term.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.BRSTNilpotent.brst_charge_nilpotent` (module `BookProof.BRSTNilpotent`), line-linked source: `ChapterBRSTNilpotent.lean` lines 207–247.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean#L207-L247

-- Generated from ChapterBRSTNilpotent.lean — theorem BookProof.BRSTNilpotent.brst_charge_nilpotent
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent












variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

theorem BookProof.BRSTNilpotent.brst_charge_nilpotent (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    Q f χ β * Q f χ β = 0 := by sorry
