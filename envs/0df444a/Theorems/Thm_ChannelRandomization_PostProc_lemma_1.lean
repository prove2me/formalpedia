-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_lemma_1
-- name    : ChannelRandomization.PostProc.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:15.442906+00:00
-- url     : https://prove2.me/theorems/02fdc9d0-066a-4dda-bbde-a8e274a6b314
-- title:
--   Lemma 1, p. 4 — s(ψ∘φ) = s(φ∘ψ)
-- statement:
--   Let $H=\mathbb C^h$, $K=\mathbb C^k$, and let $s(\chi)=\sum_{i,j}\langle i,\chi(|i\rangle\langle j|)\,j\rangle$ for a linear map $\chi:B(H)\to B(H)$. For all linear maps $\phi:B(H)\to B(K)$ and $\psi:B(K)\to B(H)$,
--
--   $$s(\psi\circ\phi)=s(\phi\circ\psi).$$
--
--   The functional $s$ thus behaves like a trace under composition of maps; this is what makes the duality $\langle\phi,\psi\rangle=s(\phi\circ\psi)$ symmetric and underlies identity (1).
--
--   **Formalization Note.** The paper states the lemma for Hermitian maps $\phi\in\mathcal L(H,K)$, $\psi\in\mathcal L(K,H)$. The Lean statement holds for all $\mathbb C$-linear maps (with $s$ taken as the real part of the sum), which contains the paper's case.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 4, Lemma 1

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem lemma_1 {h k : ℕ} (φ : Map h k) (ψ : Map k h) : s (ψ ∘ₗ φ) = s (φ ∘ₗ ψ) := by sorry
end ChannelRandomization.PostProc
