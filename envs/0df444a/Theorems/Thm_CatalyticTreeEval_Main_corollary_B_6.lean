-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_B_6
-- name    : CatalyticTreeEval.Main.corollary_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:33.760674+00:00
-- url     : https://prove2.me/theorems/41294eef-dace-4c48-bf3d-17d1ac81b0dd
-- title:
--   Corollary B.6 — composite weight detector
-- statement:
--   Let $p_1,\ldots,p_t$ be distinct primes, with $t\ge1$, let $e_i\ge0$, and set $m=\prod_i p_i$, $q_i=p_i^{e_i}$ and $\delta=\max_iq_i$. Assume $H\ge w\ge1$ and $\prod_iq_i>w$. There are one finite printer and an absolute positive constant, chosen before all these parameters, producing a multilinear polynomial of degree at most $\delta-1$ such that for every Boolean input of weight $\sigma\le w$,
--
--   $$f(x)\in\begin{cases}\{0\}&\sigma=w,\\S_m^*\setminus\{0\}&\sigma<w.\end{cases}$$
--
--   The charged printing space is at most $C(\delta\log_2H+\log_2m)$, rounded upward. Exponents equal to zero are allowed. This is the composite weight detector used to construct the polynomial matching family.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Corollary B.6, printed p. 38 (PDF p. 40); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem corollary_B_6 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p e : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H → w < ∏ i, p i ^ e i →
      ∃ f : Poly (modulus p) H,
        Multilinear f ∧ f.totalDegree ≤ delta p e - 1 ∧
        (∀ x : Fin H → Bool, weight x ≤ w →
          (weight x = w → MvPolynomial.eval (boolPoint x) f = 0) ∧
          (weight x < w → MvPolynomial.eval (boolPoint x) f ∈ canonical p (modulus p) ∧
            MvPolynomial.eval (boolPoint x) f ≠ 0)) ∧
        PolyPrint M (primeCode p ++ natsCode ((List.finRange t).map e ++ [w,H])) f
          (C * (delta p e * log₂ H + log₂ (modulus p))) := by sorry

end CatalyticTreeEval.Main
