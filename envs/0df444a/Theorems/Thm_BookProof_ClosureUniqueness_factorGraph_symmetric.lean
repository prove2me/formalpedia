-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_symmetric
-- name    : BookProof.ClosureUniqueness.factorGraph_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:45:15.487793+00:00
-- url     : https://prove2.me/theorems/896db3ce-82e7-4101-9b52-8d7629ae947a
-- title:
--   `BookProof.ClosureUniqueness.factorGraph_symmetric` {A : D →ₗ[ℂ] F} {p q : F × F} (hp : p ∈ factorGraph A) (hq : q ∈ factorGraph A) : (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.factorGraph_symmetric` {A : D →ₗ[ℂ] F} {p q : F × F} (hp : p ∈ factorGraph A) (hq : q ∈ factorGraph A) : (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.factorGraph_symmetric`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.factorGraph_symmetric
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.factorGraph_symmetric {A : D →ₗ[ℂ] F} {p q : F × F} (hp : p ∈ factorGraph A)
    (hq : q ∈ factorGraph A) : (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2 := by sorry
