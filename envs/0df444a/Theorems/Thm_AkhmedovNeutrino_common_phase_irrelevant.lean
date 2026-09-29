-- Prove2me | Theorems.Thm_AkhmedovNeutrino_common_phase_irrelevant
-- name    : AkhmedovNeutrino.common_phase_irrelevant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:08:35.056249+00:00
-- url     : https://prove2.me/theorems/38bb14b4-2357-4866-a7e7-3f4f521b3d19
-- title:
--   Terms proportional to the identity do not affect oscillations (Sec. 8.1)
-- statement:
--   Let $H$ be any complex $2\times2$ matrix and $c\in\mathbb R$. Suppose $\psi:\mathbb R\to\mathbb C^2$ satisfies, for every $t$,
--   $$\frac{d}{dt}\psi(t)=-i\,(H+c\,\mathbf 1)\,\psi(t).$$
--   Define $\varphi(t)=e^{ict}\,\psi(t)$. Then
--
--   1. $\varphi$ solves the Schrödinger equation with the reduced Hamiltonian: $\dfrac{d}{dt}\varphi(t)=-i\,H\,\varphi(t)$ for every $t$;
--   2. for every $t$ and each component $k$, $|\varphi_k(t)|^2=|\psi_k(t)|^2$.
--
--   This justifies discarding the flavour-independent diagonal terms ($p+(m_1^2+m_2^2)/4E$ and the neutral-current potential) when passing from eq. (89) to eqs. (90) and (91): they change no oscillation probability.
--
--   **Formalization Note** Components are indexed by $\{0,1\}$; derivatives are taken in the product space $\mathbb C^2$.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.1, paragraph following eq. (89) and paragraph preceding eq. (91), p. 30

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem common_phase_irrelevant (H : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ)
    (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ t : ℝ, HasDerivAt ψ
      (-(Complex.I • (H + (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec (ψ t))) t) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s) • ψ s)
      (-(Complex.I • H.mulVec (Complex.exp (Complex.I * c * t) • ψ t))) t) ∧
    ∀ (t : ℝ) (k : Fin 2),
      Complex.normSq ((Complex.exp (Complex.I * c * t) • ψ t) k) = Complex.normSq (ψ t k) := by
  sorry
end AkhmedovNeutrino
