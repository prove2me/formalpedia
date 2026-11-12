-- Prove2me | Theorems.Thm_BunkbedAux_phiExt_involution
-- name    : BunkbedAux.phiExt_involution
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:55:05.954759+00:00
-- url     : https://prove2.me/theorems/a64336c9-9dab-4bd8-8a58-c1336b3ad9ee
-- title:
--   The involution $\phi$ is weight-preserving and fixes its pivot
-- statement:
--   The involution used in the robustness lemma of Gladkov--Pak--Zimin is defined by locating the *first* hyperedge $e$ along the path $\rho$ whose refined state lies in $\Lambda^2_+$, then applying the half-reflection $\eta$ at $e$ and the level swap $\rho$ to every hyperedge after $e$, leaving the hyperedges before $e$ untouched. This theorem verifies that the resulting map $\phi = \texttt{phiExt}\,e$ really is a weight-preserving involution.
--
--   Assume $\Psi$ is a legal refined configuration, that the state at $e$ lies in $\Lambda^2_+$, and that no earlier hyperedge has its state in $\Lambda^2_+$ — so $e$ is the pivot selected by the construction. Then:
--
--   1. $\phi(\Psi)$ is again legal;
--   2. the state of $\phi(\Psi)$ at $e$ still lies in $\Lambda^2_+$;
--   3. no hyperedge before $e$ has its $\phi(\Psi)$-state in $\Lambda^2_+$;
--   4. $\phi(\phi(\Psi)) = \Psi$;
--   5. $\prod_h \texttt{wt}(\phi(\Psi)(h)) = \prod_h \texttt{wt}(\Psi(h))$.
--
--   Points 2 and 3 together say that $\phi$ **fixes its own pivot**: the first hyperedge in $\Lambda^2_+$ is the same for $\Psi$ and for $\phi(\Psi)$. This is exactly what makes point 4 meaningful — applying the construction twice recovers $\Psi$ only because the second application selects the same $e$, so that $\eta$ is applied twice at $e$ and the level swap twice beyond it, and both are involutions.
--
--   Point 5 is where the refinement of the state space earns its keep. The level swap preserves weights for the trivial reason that a pair's weight is symmetric under transposition; but $\eta$ genuinely moves mass between *different* pairs, and preserves weight only because the refinement split off from $(abc, a|b|c)$ precisely the sub-event of weight $P_{ab|c}P_{ac|b}$, which is the weight of $(ab|c, ac|b)$.
--
--   **Mathematical role.** Together with the path-surgery lemma, which says that $\phi$ exchanges the same-level and cross-level connection events, this yields the cancellation: the configurations meeting $\Lambda^2_+$ contribute equally to the two events and drop out of their difference. The robustness lemma is thereby reduced to the configurations that avoid $\Lambda^2_+$ altogether, where the alternative bunkbed hypergraph model and Hollom's computation take over.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.5 (p. 5): the definition of phi and the assertion that it is a weight-preserving involution on X.

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **`phiExt e` is a weight-preserving involution that fixes its own pivot.** If `e` is the
first hyperedge whose state lies in `Λ²₊`, then `phiExt e` maps legal configurations to legal
configurations, keeps `e` as the first hyperedge in `Λ²₊`, is an involution, and preserves the
configuration weight. -/
theorem phiExt_involution (P : WZ → ℚ) (e : Fin 6) (Ψ : Fin 6 → WZExt)
    (hleg : ∀ h, WZExt.legal (Ψ h) = true)
    (he : WZExt.inLamSq (Ψ e) = true)
    (hmin : ∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (Ψ h) = false) :
    (∀ h, WZExt.legal (phiExt e Ψ h) = true)
    ∧ WZExt.inLamSq (phiExt e Ψ e) = true
    ∧ (∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (phiExt e Ψ h) = false)
    ∧ phiExt e (phiExt e Ψ) = Ψ
    ∧ (∏ h, WZExt.wt P (phiExt e Ψ h)) = ∏ h, WZExt.wt P (Ψ h) := by
  sorry

end BunkbedAux
