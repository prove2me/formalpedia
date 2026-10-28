-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_eq_1
-- name    : ChannelRandomization.PostProc.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:29.799556+00:00
-- url     : https://prove2.me/theorems/c06876bd-ab31-42a3-a5ed-1345f385010e
-- title:
--   Eq. (1), p. 5 — ⟨φ,ψ⟩ = ⟨ψ,φ⟩ and ⟨α∘β, ψ⟩ = s(α∘β∘ψ) = ⟨β, ψ∘α⟩ = ⟨α, β∘ψ⟩
-- statement:
--   Let $\langle\phi,\psi\rangle=s(\phi\circ\psi)$ be the duality between maps $B(H)\to B(L)$ and maps $B(L)\to B(H)$. For linear maps $\beta:B(H)\to B(K)$, $\alpha:B(K)\to B(L)$, $\psi:B(L)\to B(H)$, and for any $\phi:B(H)\to B(L)$, $\chi:B(L)\to B(H)$,
--
--   $$\langle\phi,\chi\rangle=\langle\chi,\phi\rangle,\qquad \langle\alpha\circ\beta,\psi\rangle=s(\alpha\circ\beta\circ\psi)=\langle\beta,\psi\circ\alpha\rangle=\langle\alpha,\beta\circ\psi\rangle .$$
--
--   The paper calls this "one of the most important tools used below": it moves a factor of a composition from one side of the pairing to the other, which is how the adjoint actions of pre- and post-composition are computed throughout.
--
--   **Formalization Note.** The paper assumes $\alpha,\beta,\psi$ Hermitian; the Lean statement holds for all $\mathbb C$-linear maps, which contains the paper's case. The middle equality $\langle\alpha\circ\beta,\psi\rangle=s(\alpha\circ\beta\circ\psi)$ is the definition of the pairing, kept to mirror the display.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 5, Eq. (1) and the sentence before it

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem eq_1 {h k l : ℕ} (β : Map h k) (α : Map k l) (ψ : Map l h) (φ : Map h l) (χ : Map l h) :
    pair φ χ = pair χ φ ∧
      pair (α ∘ₗ β) ψ = s (α ∘ₗ β ∘ₗ ψ) ∧
      s (α ∘ₗ β ∘ₗ ψ) = pair β (ψ ∘ₗ α) ∧
      pair β (ψ ∘ₗ α) = pair α (β ∘ₗ ψ) := by sorry
end ChannelRandomization.PostProc
