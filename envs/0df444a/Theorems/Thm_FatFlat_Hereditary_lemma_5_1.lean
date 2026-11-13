-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_5_1
-- name    : FatFlat.Hereditary.lemma_5_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:18.420692+00:00
-- url     : https://prove2.me/theorems/4ff33ec9-de17-406e-9865-71b044ca6008
-- title:
--   Lemma 5.1 — every drill-flat graph class is fat-shallow-minor-free
-- statement:
--   Every drill-flat graph class $\mathcal C$ is fat-shallow-minor-free (FSMF). No hereditary assumption is made.
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 5.1, p. 16 (PDF p. 18). Verbatim: 'Lemma 5.1. Every drill-flat graph class is fat-shallow-minor-free.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 5.1** (arXiv:2607.21474, p. 16). Every drill-flat graph class is
fat-shallow-minor-free. -/
theorem lemma_5_1 (C : GraphClass) (hC : DrillFlat C) : FSMF C := by sorry

end FatFlat.Hereditary
