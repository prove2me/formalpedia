-- Prove2me | Theorems.Thm_CliffordCert_Optimal_radical_repair
-- name    : CliffordCert.Optimal.radical_repair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:39.109444+00:00
-- url     : https://prove2.me/theorems/233f2bbb-bd45-46fe-98e7-7d5f8c2e15ad
-- title:
--   Lemma 9 — repair without increasing dimension
-- statement:
--   Let $W$ be even dimensional in a nondegenerate binary symplectic space, and put $k=\dim W$ and $t=\dim\operatorname{rad}(W)$. Then $t$ is even. There is a cover of $W$ by ambient nondegenerate $k$-subspaces with at most
--   $$f(t)=\begin{cases}1&t=0,\\2^{t/2}+1&t>0\end{cases}$$
--   members, and
--   $$f(t)\le2^t,\qquad f(t)\le\frac{2\cdot2^t+1}{3}.$$
--   Members may extend outside $W$. The finite repair search finds such a list, including when $W=\{0\}$. This is the exact repair guarantee used by preprocessing.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
--   - encoding: existence of a bounded finite repair list → the first passing list in an exhaustive bounded-length enumeration; reason: the finite search checks exactly the source properties and assumes none of them
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 13, Lemma 9, Eqs. (23)–(24), proof through p. 14 (PDF p. 15) (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem radical_repair {N : ℕ} (B : Form N) (hB : IsSymplectic B)
    (W : Submodule F₂ (Binary N)) (hW : Even (Module.finrank F₂ W)) :
    let t := Module.finrank F₂ (radical B W)
    Even t ∧
    (∃ S : List (Submodule F₂ (Binary N)),
      repairCheck B W S ∧ S.length ≤ repairCost t ∧ repairSearch B W = some S) ∧
    repairCost t ≤ 2^t ∧ (repairCost t : ℝ) ≤ (2*(2 : ℝ)^t+1)/3 := by sorry
end CliffordCert.Optimal
