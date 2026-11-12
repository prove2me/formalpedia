-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_B_5
-- name    : CatalyticTreeEval.Main.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:07.196929+00:00
-- url     : https://prove2.me/theorems/770f3a9b-a018-47ac-a646-cd54d1176efb
-- title:
--   Lemma B.5 — prime-power weight detector
-- statement:
--   Let $p$ be prime, $e,w\ge0$, $H\ge1$, and $q=p^e$. A single finite printing machine and one positive absolute constant work for all these parameters. There is a symmetric multilinear polynomial over $\mathbb Z/p\mathbb Z$, of degree at most $q-1$, such that on every Boolean vector $x$ of Hamming weight $|x|$,
--
--   $$f(x)=\begin{cases}0& |x|\equiv w\pmod q,\\1&\text{otherwise}.\end{cases}$$
--
--   The machine prints a sparse presentation in at most $C(q\log_2(H+1)+\log_2p)$ work bits, rounded upward. This includes $e=0$, when the zero polynomial works, and $w=0$. This detector supplies the per-prime ingredient for the composite detector.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma B.5, printed p. 37 (PDF p. 39); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem lemma_B_5 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (p e w H : ℕ), Nat.Prime p → 1 ≤ H →
      ∃ f : Poly p H, Symmetric f ∧ Multilinear f ∧ f.totalDegree ≤ p ^ e - 1 ∧
        (∀ x : Fin H → Bool, MvPolynomial.eval (boolPoint x) f =
          if weight x % (p ^ e) = w % (p ^ e) then 0 else 1) ∧
        PolyPrint M (natsCode [p,e,w,H]) f
          (C * ((p ^ e : ℕ) * log₂ (H + 1) + log₂ p)) := by sorry

end CatalyticTreeEval.Main
