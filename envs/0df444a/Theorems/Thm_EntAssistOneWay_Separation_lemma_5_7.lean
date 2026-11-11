-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_lemma_5_7
-- name    : EntAssistOneWay.Separation.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:04.521562+00:00
-- url     : https://prove2.me/theorems/6f98fc9b-8b8d-448a-9fd0-21c53680984e
-- title:
--   Lemma 5.7 — invertibility of the binary-dot-product indicator over F₃
-- statement:
--   For $S=\mathbb F_2^r$, let $M$ be the matrix over $\mathbb F_3$ with rows and columns indexed by $S$ and entries
--   $$M_{x,y}=\begin{cases}1&x\cdot y=0,\\0&x\cdot y=1.\end{cases}$$
--   Then $M$ is invertible. Equivalently, its determinant is a unit in $\mathbb F_3$. The empty-coordinate case $r=0$ gives the one-by-one matrix with entry one. This is the exact matrix used in the phase-correlation argument.
--
--   Differences from the source:
--   - generalization: S = Z_2^r with r ≥ 1 (standing assumption of §5, p. 24) → every r in ℕ, including r = 0; reason: at r = 0 the matrix is the 1×1 matrix (1), which is invertible, and every r ≥ 1 instance is the source's statement verbatim
--   - encoding: M is invertible → IsUnit M.det over ZMod 3; reason: the determinant criterion is equivalent to invertibility over this field
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 31, Lemma 5.7

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Lemma 5.7, p. 31, including r = 0. -/
theorem lemma_5_7 (r : ℕ) : IsUnit (dotIndicator r).det := by sorry

end

end EntAssistOneWay.Separation
