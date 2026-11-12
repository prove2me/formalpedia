-- Prove2me | Theorems.Thm_BunkbedAux_cancel_at_pivot
-- name    : BunkbedAux.cancel_at_pivot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:02:43.559417+00:00
-- url     : https://prove2.me/theorems/3c7eaeb8-ac70-413c-b3f7-032013885018
-- title:
--   The involution cancels the configurations meeting $\Lambda^2_+$
-- statement:
--   This is the cancellation step of the involution argument of Gladkov--Pak--Zimin, in the form in which it is actually used.
--
--   Let $\Lambda^2_+$ be the sixteen-element set of refined pair states of Definition 3.4, and let $X$ be the set of legal refined configurations in which *some* hyperedge has its state in $\Lambda^2_+$. Partition $X$ according to the **pivot**: the first hyperedge $e$, in the order of the path $\rho$, whose state lies in $\Lambda^2_+$. This theorem is the cancellation on a single block of that partition. Writing the block as
--   $$X_e = \bigl\{\Psi \text{ legal} : \Psi(e) \in \Lambda^2_+,\ \Psi(h) \notin \Lambda^2_+ \text{ for all } h < e\bigr\},$$
--   the assertion is
--   $$\sum_{\Psi \in X_e} \mathrm{wt}(\Psi)\,\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}\bigr] \;=\; \sum_{\Psi \in X_e} \mathrm{wt}(\Psi)\,\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}'\bigr],$$
--   where $\mathrm{wt}(\Psi) = \prod_h \mathrm{wt}(\Psi(h))$ is the product of the refined per-hyperedge weights.
--
--   In words: on each block, the same-level and the cross-level connection events carry exactly the same weight. Summing over the six possible pivots, the whole of $X$ contributes nothing to the difference of the two connection probabilities, which is what reduces the robustness lemma to the configurations avoiding $\Lambda^2_+$ entirely.
--
--   **Why the statement is phrased by pivot rather than for $X$ at once.** The involution is only defined relative to a chosen hyperedge, and it is an involution precisely because it *preserves the pivot* — applying it twice selects the same $e$ and so undoes itself. Splitting $X$ into blocks makes this available block by block and avoids having to introduce the pivot as a partial function on $X$.
--
--   No hypothesis on $P$ is needed: the identity holds for an arbitrary weight function, since it is a rearrangement of a finite sum rather than a probabilistic statement.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.5 (p. 6): 'With phi established as a weight-preserving involution on X and Lemma 3.8 ... it follows that P(C and X) = P(C' and X)'.

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The cancellation on configurations with pivot `e`.** Over the legal refined configurations
whose first hyperedge in `Λ²₊` is `e`, the weighted count of same-level connections equals the
weighted count of cross-level connections. The involution `phiExt e` is a weight-preserving
bijection of this set that exchanges the two events. -/
theorem cancel_at_pivot (P : WZ → ℚ) (e : Fin 6) :
    ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        (∀ h, WZExt.legal (Ψ h) = true) ∧ WZExt.inLamSq (Ψ e) = true ∧
        ∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (Ψ h) = false),
        (∏ h, WZExt.wt P (Ψ h)) *
          (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)
      = ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        (∀ h, WZExt.legal (Ψ h) = true) ∧ WZExt.inLamSq (Ψ e) = true ∧
        ∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (Ψ h) = false),
        (∏ h, WZExt.wt P (Ψ h)) *
          (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0) := by
  sorry

end BunkbedAux
