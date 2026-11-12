-- Prove2me | Theorems.Thm_BunkbedAux_cancel_on_X
-- name    : BunkbedAux.cancel_on_X
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:26:31.959225+00:00
-- url     : https://prove2.me/theorems/0bbdf1ce-cd81-40da-893e-dddf515ebb37
-- title:
--   The configurations meeting $\Lambda^2_+$ contribute nothing to the difference
-- statement:
--   This is the cancellation step of the involution argument of Gladkov--Pak--Zimin, stated for the whole set $X$ rather than one block at a time.
--
--   Let $X$ be the set of legal refined configurations in which **some** hyperedge has its state in the sixteen-element set $\Lambda^2_+$. Then
--
--   $$\sum_{\Psi \in X} \mathrm{wt}(\Psi)\,\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}\bigr] \;=\; \sum_{\Psi \in X} \mathrm{wt}(\Psi)\,\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}'\bigr],$$
--
--   where $\mathrm{wt}(\Psi) = \prod_h \mathrm{wt}(\Psi(h))$ is the product of the refined per-hyperedge weights. In words: on $X$ the same-level and the cross-level connection events carry exactly the same weight, so $X$ contributes nothing whatsoever to the difference of the two connection probabilities.
--
--   **The mechanism.** Each configuration in $X$ has a well-defined **pivot**: the first hyperedge, in the order of the path $\rho$, whose state lies in $\Lambda^2_+$. The involution $\phi$ applies the half-reflection at the pivot and the level swap to every later hyperedge, leaving the earlier ones untouched. It is weight-preserving, it maps $X$ to itself, it returns each configuration's own pivot unchanged — which is what makes it an involution — and by the path-surgery lemma it exchanges the two connection events. Reindexing the sum along it therefore turns one side into the other.
--
--   **Consequence.** The robustness lemma is thereby reduced to the complementary configurations, those in which *every* hyperedge avoids $\Lambda^2_+$. There the sub-block in which every hyperedge is fully on one level is precisely the alternative bunkbed hypergraph model, contributing Hollom's surplus of one cross-level connection out of sixty-four, and everything else is an error term controlled by the hypothesis $400P_{a|bc} \le P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$.
--
--   No hypothesis on $P$ is needed: the identity is a rearrangement of a finite sum, valid for an arbitrary weight function.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.5 (p. 6): P(C and X) = P(C' and X).

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The configurations meeting `Λ²₊` cancel.** Over all legal refined configurations in which
some hyperedge has its state in `Λ²₊`, the weighted count of same-level connections equals the
weighted count of cross-level connections. -/
theorem cancel_on_X (P : WZ → ℚ) :
    ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        (∀ h, WZExt.legal (Ψ h) = true) ∧ ∃ k, WZExt.inLamSq (Ψ k) = true),
        (∏ h, WZExt.wt P (Ψ h)) *
          (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)
      = ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        (∀ h, WZExt.legal (Ψ h) = true) ∧ ∃ k, WZExt.inLamSq (Ψ k) = true),
        (∏ h, WZExt.wt P (Ψ h)) *
          (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0) := by
  sorry

end BunkbedAux
