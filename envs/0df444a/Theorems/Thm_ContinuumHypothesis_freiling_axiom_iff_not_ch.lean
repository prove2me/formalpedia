-- Prove2me | Theorems.Thm_ContinuumHypothesis_freiling_axiom_iff_not_ch
-- name    : ContinuumHypothesis.freiling_axiom_iff_not_ch
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:37:13.550993+00:00
-- url     : https://prove2.me/theorems/233c89e7-f5bc-4012-bf4d-1d152fd43936
-- title:
--   Freiling's axiom of symmetry $\iff\neg$CH
-- statement:
--   Freiling's axiom of symmetry — for every $f$ assigning to each real a countable set of reals there exist $x,y\in\mathbb R$ with $x\notin f(y)$ and $y\notin f(x)$ — is equivalent to the negation of the continuum hypothesis:
--   $$\mathrm{AX}\ \Longleftrightarrow\ \neg\mathrm{CH}.$$
--
--   **Formalization Note** Stated in Lean's set theory (with choice), where CH is `CH` from the definition file.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Arguments for and against the continuum hypothesis', paragraph 4 ('Chris Freiling presented an argument against CH by showing that the negation of CH is equivalent to Freiling's axiom of symmetry'); Freiling, J. Symbolic Logic 51 (1986) 190–200.

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem freiling_axiom_iff_not_ch : FreilingAxiom ↔ ¬ CH := by sorry

end ContinuumHypothesis
