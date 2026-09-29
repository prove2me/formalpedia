-- Prove2me | Theorems.Thm_AkhmedovNeutrino_msw_transition_probability
-- name    : AkhmedovNeutrino.msw_transition_probability
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:18:02.065678+00:00
-- url     : https://prove2.me/theorems/a1e45009-407e-4f79-9b51-011910892b61
-- title:
--   $\nu_e\to\nu_\mu$ transition probability in matter of constant density: $P=\sin^22\theta\,\sin^2(\pi L/l_m)$ (eq. (95))
-- statement:
--   Consider two-flavour neutrino oscillations $\nu_e\leftrightarrow\nu_\mu$ in matter of constant density. Let $\Delta m^2,\theta_0,G_F,N_e\in\mathbb R$ and $E>0$, and let $H$ be the MSW Hamiltonian of eq. (91). Let $\nu(t)=(\nu_e(t),\nu_\mu(t))\in\mathbb C^2$ be the vector of flavour amplitudes, and suppose that it solves the evolution equation
--   $$i\,\frac{d}{dt}\nu(t)=H\,\nu(t)\qquad\text{for all }t\in\mathbb R,$$
--   with initial state a pure electron neutrino, $\nu(0)=(1,0)$. Then for every distance $L$ (identified with the elapsed time, $L\simeq t$),
--   $$P(\nu_e\to\nu_\mu;L)=|\nu_\mu(L)|^2=\sin^22\theta\,\sin^2\!\Big(\pi\frac{L}{l_m}\Big),$$
--   where $\sin^22\theta$ is the oscillation amplitude in matter (eq. (97)) and $l_m=2\pi/\Delta_m$ is the oscillation length in matter (eq. (96)), $\Delta_m$ being the difference of the eigenenergies (eq. (94)).
--
--   The probability has exactly the vacuum form (60) with the vacuum mixing angle and oscillation length replaced by their matter counterparts.
--
--   **Formalization Note** The statement quantifies over every everywhere-differentiable solution of the initial-value problem, so a proof must include uniqueness of the solution. In the degenerate case $\Delta_m=0$ the division convention gives $l_m=0$, amplitude $0$ and $\sin(\pi L/0)=0$; the claim then says $\nu_\mu(L)=0$.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 8.2, eqs. (95)-(97) with the evolution equation (91), pp. 30-31

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

namespace AkhmedovNeutrino
theorem msw_transition_probability (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E)
    (ν : ℝ → Fin 2 → ℂ)
    (hν : ∀ t : ℝ, HasDerivAt ν
      (-(Complex.I • ((mswHamiltonian Δm2 E θ0 GF Ne).map ((↑) : ℝ → ℂ)).mulVec (ν t))) t)
    (h0 : ν 0 = ![1, 0]) (L : ℝ) :
    Complex.normSq (ν L 1) =
      matterOscAmplitude Δm2 E θ0 GF Ne *
        Real.sin (Real.pi * L / matterOscLength Δm2 E θ0 GF Ne) ^ 2 := by sorry
end AkhmedovNeutrino
