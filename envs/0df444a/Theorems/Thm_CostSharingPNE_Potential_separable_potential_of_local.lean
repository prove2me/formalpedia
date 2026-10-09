-- Prove2me | Theorems.Thm_CostSharingPNE_Potential_separable_potential_of_local
-- name    : CostSharingPNE.Potential.separable_potential_of_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:12.120127+00:00
-- url     : https://prove2.me/theorems/737f75e7-c18e-4246-b386-28469e730504
-- title:
--   (83), p. 58 — local identities yield a separable generalized weighted potential
-- statement:
--   Let a finite welfare sharing game have utility $U_i(a)=\sum_{r\in a_i}f^r(i,\{a\}_r)$. For each resource $r$, let $\phi_r$ be a vector-valued function of its user coalition. Give each player $i$ a positive weight $w_i$ and a fixed component $k(i)$. Suppose that, whenever $i\in S$, all components of $\phi_r(S)-\phi_r(S\setminus\{i\})$ before $k(i)$ vanish and
--
--   $$f^r(i,S)=w_i\bigl(\phi_r(S)_{k(i)}-\phi_r(S\setminus\{i\})_{k(i)}\bigr).$$
--
--   Then $\Phi(a)=\sum_{r\in R}\phi_r(\{a\}_r)$ is a generalized weighted potential for the game with weights $w_i$. This is the local-to-global reduction used in Appendix C.
--
--   **Formalization Note** The index $k(i)$ is fixed for each player, and earlier components are explicitly unchanged. This corrects the printed “first nonzero” phrase in (83). The identity is meaningful for arbitrary action sets, including empty ones; it makes no equilibrium-existence claim.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, (81)–(83), p. 58

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

namespace CostSharingPNE.Potential

/-- Appendix C, display (83): local potential identities yield a separable potential. -/
theorem separable_potential_of_local
    (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (A : Fin n → Finset (Finset (Fin m)))
    (F : Fin m → CostSharingPNE.Char.Rule n) {K : ℕ}
    (φ : Fin m → Finset (Fin n) → Fin K → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (idx : Fin n → Fin K)
    (hloc : ∀ r i S, i ∈ S →
      (∀ c, c < idx i → φ r S c = φ r (S.erase i) c) ∧
      F r i S = w i * (φ r S (idx i) - φ r (S.erase i) (idx i))) :
    IsGenWeightedPotential A (fun i a => utility F a i)
      (fun a => ∑ r, φ r (CostSharingPNE.Char.players a r)) w := by sorry

end CostSharingPNE.Potential
