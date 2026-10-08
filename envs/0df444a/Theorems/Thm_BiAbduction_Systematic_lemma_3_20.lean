-- Prove2me | Theorems.Thm_BiAbduction_Systematic_lemma_3_20
-- name    : BiAbduction.Systematic.lemma_3_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:54.407997+00:00
-- url     : https://prove2.me/theorems/ef5a2f28-ab95-4421-b4e2-7a7d1d9f44b0
-- title:
--   Lemma 3.20 — Incompat(Δ) and ¬Elsewhere(Δ) are semantically equivalent
-- statement:
--   For every quantifier-free left-hand side $\Delta=\big(\bigwedge_i A_i\big)\wedge\big(\ast_j E_j\mapsto E'_j\big)$ of the Points-to Instantiation, the disjunction $\mathrm{Incompat}(\Delta)$ denotes exactly the incompatible solutions:
--   $$[\![\mathrm{Incompat}(\Delta)]\!]=\neg\,\mathrm{Elsewhere}(\Delta).$$
--   That is, a state satisfies $\mathrm{Incompat}(\Delta)$ iff no heap separate from its heap satisfies $\Delta$ with the same stack.
--
--   This is the second phase of the systematic algorithm: the incompatible solutions are expressible as a disjunction of symbolic heaps.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 32, Lemma 3.20 (Incompat defined on p. 31)

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Incompat

namespace BiAbduction.Systematic

/-- Lemma 3.20 (p. 32). `Incompat(Δ)` and `¬Elsewhere(Δ)` are semantically equivalent. -/
theorem lemma_3_20 (Δ : LHS) :
    disjDen (incompat Δ) = (Elsewhere (lhsDen Δ))ᶜ := by sorry

end BiAbduction.Systematic
