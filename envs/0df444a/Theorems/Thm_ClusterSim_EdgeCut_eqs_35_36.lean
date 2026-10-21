-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eqs_35_36
-- name    : ClusterSim.EdgeCut.eqs_35_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:55:49.502889+00:00
-- url     : https://prove2.me/theorems/9d65d0dd-b7f6-4313-a03e-5294d29af937
-- title:
--   Eqs. (35)–(36) — one sample 8^K c_s t_s has mean T(G, A) and |8^K c_s t_s| ≤ 2^{2K} = a
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network with a clustering, $K=|E_{\mathrm{cut}}|$, and suppose that for every $s\in[8]^{E_{\mathrm{cut}}}$ the device outcome $t_s$ has a probability law $\mathrm{run}(s)$ concentrated on $[-1,1]$ with mean $T(G',\mathcal A_s)$ ("for each $s$, $t_s\in[-1,1]$ is a random variable with expectation $T(G',\mathcal A_s)$", p. 10). Let $\mu$ be the law of one sample $8^K c_s t_s$, with $s$ uniform on $[8]^{E_{\mathrm{cut}}}$ and then $t_s\sim\mathrm{run}(s)$. Then $\mu$ is a probability law,
--   $$|8^K c_s t_s|\le 8^K\cdot 2^{-K}=2^{2K}=a\quad\mu\text{-almost surely},\qquad\text{and}\qquad T(G,\mathcal A)=\mathbb E_{(s,t_s)}\big[8^K c_s t_s\big].$$
--
--   These are the two inputs of Hoeffding's inequality in the proof of Theorem 1: the samples are bounded by $a=2^{2K}$ and unbiased for $T(G,\mathcal A)$.
--
--   **Formalization Note** The mean of $\mathrm{run}(s)$ is a real number and is required to equal the complex value $T(G',\mathcal A_s)$ (so those values are real); the conclusion compares the real mean of $\mu$ with the complex $T(G,\mathcal A)$ in $\mathbb C$, without taking a real part.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 10, proof of Theorem 1, eqs. (35)–(36)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Estimator

namespace ClusterSim.EdgeCut

open MeasureTheory

/-- Eqs. (35)–(36), p. 10: if for every `s ∈ [8]^{E_cut}` the device outcome `t_s` has a law on
`[−1, 1]` with mean `T(G′, A_s)`, then one sample `8^K c_s t_s` (`K = |E_cut|`, `s` uniform) has a
probability law, is bounded by `a = 2^{2K}` in absolute value, and has mean `T(G, A)`. -/
theorem eqs_35_36 {G : TensorNetwork} {r : ℕ} (P : Clustering G r)
    (run : (P.Ecut → Fin 8) → Measure ℝ) [∀ s, IsProbabilityMeasure (run s)]
    (hrange : ∀ s, ∀ᵐ t ∂(run s), t ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ s, ((∫ t, t ∂(run s) : ℝ) : ℂ) = value (cut G P.Ecut s)) :
    IsProbabilityMeasure (sampleLaw P run) ∧
      (∀ᵐ x ∂(sampleLaw P run), |x| ≤ (2 : ℝ) ^ (2 * P.Ecut.card)) ∧
      ((∫ x, x ∂(sampleLaw P run) : ℝ) : ℂ) = value G := by sorry

end ClusterSim.EdgeCut
