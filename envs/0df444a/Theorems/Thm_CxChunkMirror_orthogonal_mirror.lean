-- Prove2me | Theorems.Thm_CxChunkMirror_orthogonal_mirror
-- name    : CxChunkMirror.orthogonal_mirror
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:16:49.425222+00:00
-- url     : https://prove2.me/theorems/e467ef25-ea49-4ebc-973a-aad1e348b205
-- title:
--   Orthogonal reversal of a valid complex-network stage preserves charged child widths
-- statement:
--   Let $P$ be a valid round-six complex-network program on a finite role set. Each role starts with a subspace label in $\mathbf F_2^m$. Write $L_0$ and $L_1$ for the starting and ending label maps, $L^\perp$ for pointwise orthogonal complementation under the binary dot product, and $w(P)$ for the ordered list of positive child widths. Form $B$ by reversing the program and complementing its frames.
--
--   $$B\text{ is valid from }L_1^\perp,\qquad L_{\mathrm{end}}(B)=L_0^\perp,\qquad w(B)=\operatorname{reverse}(w(P)).$$
--
--   The result supplies a backward-stage certificate from a forward-stage certificate at any dimension $m$, preserving each charged width with its multiplicity and order under reversal.
-- source:
--   Formal construction and proof in the round-eight cxNetR8G trial. Stage-two complement time-reversal: S. Jain, integer-mult-kappa, commit 5868dc701a9bec375c9dc5391d992ab3b8c35f3f, https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/README.md#L61-L69 . Round-six chunk, validity and width definitions: Def_IntMul_Kappa_R6_Defs24, source module Solutions.R6CxNetSim, lines 143–229. Elementary append and finite-rank proof arguments follow xuanji’s accepted round-six proof, https://prove2.me/api/v1/submissions/534cb506-9a9f-4445-8a59-416047960d9d/solution .

import Definitions.Def_IntMul_Kappa_CxChunkMirror

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Cx NetLabels CxChunkMirror

namespace CxChunkMirror

theorem orthogonal_mirror {R : Type} [DecidableEq R] {m : ℕ} [Fintype R]
    (cs : List (GChunk R m)) (lab : R → Lab m) (valid : ProgValid cs lab) :
    let b := backwardProgram (orth 1) cs
    ProgValid b (orth 1 ∘ progLab cs lab) ∧
      progLab b (orth 1 ∘ progLab cs lab) = orth 1 ∘ lab ∧
      progWidths b = (progWidths cs).reverse := by
  sorry

end CxChunkMirror
