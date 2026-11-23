-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_permuted_annihilator_data
-- name    : ApproxPolySatCH.Main.permuted_annihilator_data
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:12.050214+00:00
-- url     : https://prove2.me/theorems/09a38f7d-3ff7-47de-8722-bddecf5f9917
-- title:
--   Proposition 4 interface — permutation invariance of the annihilator data
-- statement:
--   Let $k$ be a field, let $f=(f_0,\ldots,f_n)$ be a minimally dependent tuple in $k[X_1,\ldots,X_n]$, and let $H$ be its irreducible annihilator, including the canonical presentation after scalar extension to $K=\overline k$. For a coordinate permutation $\sigma$, put
--   $$f^\sigma_i=f_{\sigma(i)},\qquad H^\sigma=H(Y_{\sigma^{-1}(0)},\ldots,Y_{\sigma^{-1}(n)}).$$
--   Then $f^\sigma$ is again minimally dependent, $H^\sigma$ gives the annihilator presentation of $f^\sigma$ over both $k$ and $K$, permuting coordinates does not change approximate polynomial satisfiability, and
--   $$\max_i\deg f^\sigma_i=\max_i\deg f_i.$$
--
--   This is the coordinate-change interface used to pass from Claims 7–8 to Claims 9–10. Inverse renaming is exactly the convention that makes $H^\sigma(f^\sigma)=0$: the irreducible relation remains unchanged after relabelling the indeterminates, while the image of the polynomial map is merely permuted.
--
--   **Formalization Note.** `MvPolynomial.rename sigma.symm H` denotes $H^\sigma$. The APS equivalence concerns the unpermuted and permuted tuples as a whole, not an assertion that every individual coordinate has the same image.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 4 and Claims 7–10, pp.18–20 (coordinate permutation between Claims 7–8 and Claims 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=18

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.permuted_annihilator_data {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (hf : MinimallyDependent f)
    (sigma : Equiv.Perm (Fin (n + 1))) (H : Poly k (n + 1))
    (hH : ApproxPolySatCH.Main.AnnihilatorPresentation f H) :
    ApproxPolySatCH.Main.MinimallyDependent (fun i => f (sigma i)) ∧
      ApproxPolySatCH.Main.AnnihilatorPresentation (fun i => f (sigma i)) (MvPolynomial.rename sigma.symm H) ∧
      (ApproxPolySatCH.Main.APS (fun i => f (sigma i)) ↔ ApproxPolySatCH.Main.APS f) ∧
      ApproxPolySatCH.Main.maxDegree (fun i => f (sigma i)) = ApproxPolySatCH.Main.maxDegree f := by sorry
