-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_29
-- name    : DIObliviousTransfer.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:05:57.245191+00:00
-- url     : https://prove2.me/theorems/1f87d981-2099-414d-9beb-9ec299b7a12b
-- title:
--   Lemma 29 — selected one-copy guessing
-- statement:
--   Consider a strategy for $G^{\mathrm{sel}}_1$ and let $\varepsilon=\Pr[\mathrm{MS}(X^{\mathrm{in}},Y,A^{\mathrm{in}},B)=0]$. Then:
--   1. with the row question always revealed, $\Pr[J=1,\hat A[0,1]=A^{\mathrm{in}}[0,1]]\le\tfrac12\Pr[J=1]+15\sqrt\varepsilon$ (37);
--   2. for every anchoring probability $\delta_*\in(0,1)$, the scores (36) satisfy $\mathbb EQ\le s_*\mathbb EJ+15\sqrt{\mathbb EL}$ with $s_*=(1+\delta_*)/2$ (38).
--
--   Differences from the source:
--
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
--   - encoding: every subsequent row-guessing measurement given X^in and that memory → the late POVM of a one-copy strategy run with δ∗ = 0 (the row question is always revealed); reason: with C = 1 surely, the late question is X^in; the first round is unchanged
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 29, pp.63–64 (PDF pp.65–66)

import Mathlib
import Definitions.Def_DIObliviousTransfer_SelectorBound

namespace DIObliviousTransfer

/-- **Lemma 29 (Selected one-copy guessing)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held
version, sha256 8334c039…), pp.63–64 (PDF pp.65–66). For a one-copy strategy of `G^sel_1` with
`ε = Pr[MS(X^in, Y, A^in, B) = 0]`:
(37) with the row question always revealed, `Pr[J = 1, Â[0,1] = A^in[0,1]] ≤ ½ Pr[J = 1] + 15√ε`;
(38) for the scores (36) in `G^sel_1` with anchoring probability `δ∗ ∈ (0, 1)`,
`E Q ≤ s∗ E J + 15 √(E L)`, `s∗ = (1 + δ∗)/2`, `Q = JW`.

**Formalization Note** (decision D2). A one-copy strategy is `SelStrategy 1`. In (37) the late
question is always revealed, i.e. the game is run with `δ∗ = 0` (`C = 1` surely); `ε` is the loss
probability over uniform questions, which does not depend on the late round. -/
theorem lemma_29 (S : SelStrategy 1) :
    selProb 0 S (fun _ _ _ a _ j ah => j 0 = true ∧ ah 0 = a 0) ≤
        (1 / 2) * selProb 0 S (fun _ _ _ _ _ j _ => j 0 = true) +
          15 * Real.sqrt (selProb 0 S (fun x y _ a b _ _ =>
            MS (x 0) (y 0) (rowOf (a 0)) (colOf (b 0)) = false)) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      selProb δ S (fun x y c a b j ah => j 0 = true ∧ selW x y c a b ah 0 = true) ≤
        ((1 + δ) / 2) * selProb δ S (fun _ _ _ _ _ j _ => j 0 = true) +
          15 * Real.sqrt (selProb δ S (fun x y c a b _ _ => selL x y c a b 0 = true)) := by sorry

end DIObliviousTransfer
