-- Prove2me | Theorems.Thm_DirS_dir_force_needs_edge
-- name    : DirS.dir_force_needs_edge
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T21:26:30.355369+00:00
-- url     : https://prove2.me/theorems/6ed5c4a6-909d-46e0-b11e-a2b93f475d67
-- title:
--   Directed forcing forces a homomorphism to the edge (Proposition 23)
-- statement:
--   Proposition 23 of the paper: if the oriented graph B has the directed forcing property, then B has a homomorphism to the directed edge K_2. The proof argues with the one-parameter family of graphons W^(lambda) of Figure 1: the mean of each is 1/16, and if B has no homomorphism to the edge, the B-density moves continuously from at most (1/16)^{e(B)} at lambda = 0 to (1/2)^{v(B)} (1/4)^{e(B)} at lambda = 1, so some lambda_0 realizes the random value while the kernel is not constant, contradicting forcing. In the mission the forcing hypothesis is the finitary epsilon-delta form, and the contradiction is reached by realizing the witnesses G_n of the approximation scheme on the non-constant kernels.
--
--   **Formalization Note** The continuity argument over lambda is the analytic core here; the reflection of the sequential definition in the finitary form is what lets the proof consume only finite graphs and the approximation data.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 4 (Proposition 23, pages 10-11).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 5 (Proposition 23): directed forcing forces a homomorphism
to the edge. If the oriented graph B has the directed forcing property,
then B has a homomorphism to the directed edge K_2. The proof of the
paper argues with the one-parameter family of graphons W^(lambda): if B
has no homomorphism to the edge, a continuity argument produces a value of
lambda at which the B-density matches the random value while the kernel is
not constant, contradicting forcing. -/
theorem dir_force_needs_edge {m : ℕ} (B : OriGraph m) (h : DirForcing B) :
    homToEdge B := by sorry

end DirS
