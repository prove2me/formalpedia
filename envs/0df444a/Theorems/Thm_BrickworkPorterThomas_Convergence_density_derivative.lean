-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_density_derivative
-- name    : BrickworkPorterThomas.Convergence.density_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:21.441199+00:00
-- url     : https://prove2.me/theorems/2b0860c0-1fc3-43eb-a0f1-fdc336e9c12f
-- title:
--   Lemma 5.2 — $\|f'\|_{L^1}=O(d)$ from the inverse moment bound $E[R^{-1}]=O(d)$
-- statement:
--   For every constant $K$ the following holds. Let $U\sim\mathcal C(l)$ be a brickwork random circuit on $n$ qubits ($n$ even, $d=2^n$, depth at least one), and fix an output string $b$. Factor $U=G_*C$, where $G_*$ is a gate of the final layer and $C$ is the remaining circuit, and let
--
--   $$
--   R=\sum_{z\in\{0,1\}^2}\left|\langle z,\bar b|C|0^n\rangle\right|^2
--   $$
--
--   be the probability mass entering $G_*$, where $\bar b$ is $b$ outside the pair of $G_*$. If $E[R^{-1}]\le K d$, then $F=|\langle b|U|0^n\rangle|^2$ has a nonincreasing probability density $f$, supported in $[0,1]$ and absolutely continuous there, satisfying the exact identity from Eq. (112) and its consequence
--
--   $$
--   \|f'\|_{L^1}=3\,\mathbb E[R^{-1}]\le3K\,d .
--   $$
--
--   This reduces the smoothness hypothesis of Theorem 5.1 to the inverse moment bound of Theorem 6.1.
--
--   **Formalization Note** The expectation $E[R^{-1}]$ is a $[0,\infty]$-valued integral with $R^{-1}=+\infty$ where $R=0$. The existence of the density is part of the conclusion. Absolute continuity on $[0,1]$ is required of the density, so that $\int_0^1|f'|$ is its total variation and cannot be lowered by choosing a version.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: U ∼ C(l) with a final layer → U ∼ C(l+1), final layer index l (0-based); reason: the final gate exists only for depth ≥ 1; every depth ≥ 1 is l+1
--   - encoding: E[R^{-1}] as a real expectation → the [0,∞]-valued integral of (R)^{-1} with 1/0 = +∞; reason: finiteness is part of the conclusion, not presupposed
--   - reading: G* the final two-qubit gate on qubits (0,1) → G* any gate of the final layer (index p); reason: for an even depth no final-layer gate acts on (0,1) in the source’s layer convention; Theorem 6.1 states the same set-up for an arbitrary fixed final gate
--   - encoding: ‖f′‖_{L¹} ≤ O(d) assuming E[R^{-1}] ≤ O(d), with Eq. (112) giving ‖f′‖_{L¹} = 3 E[R^{-1}] → ∀ K: E[R^{-1}] ≤ K d → a supported probability density f, nonincreasing and absolutely continuous on [0,1], with ‖f′‖₁ = 3 E[R^{-1}] ≤ 3 K d; reason: explicit O-witness, exact printed factor 3, and the density properties established by the mixture formula (106)–(112)
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §5, p. 15, Lemma 5.2, Eqs. (103)–(112), pp. 15–16, Eqs. (101), (103); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Lemma 5.2 (pp. 15–16), including the exact identity in Eq. (112). For any `K`, for a brickwork
circuit `U = G_* C ∼ C(l+1)` on `n = 2M` qubits, any gate `G_*` of the final layer and any fixed
output `b`, with `R = Σ_{z} |⟨z, \bar b|C|0^n⟩|²` the mass entering `G_*` (Eq. (103)), if
`E[R^{-1}] ≤ K d` then the law of `F = |⟨b|U|0^n⟩|²` has a nonincreasing density `f`, absolutely
continuous on `[0,1]`, with `‖f'‖_{L¹} = 3 E[R^{-1}] ≤ 3 K d` (`d = 2^n`).
Here `R^{-1} = +∞` where `R = 0`; the hypothesis forces its expectation to be finite. -/
theorem density_derivative : ∀ K : ℝ,
    ∀ (M l : ℕ) (b : Bits (2 * M)) (p : Fin M), 1 ≤ M →
      ∫⁻ g, (ENNReal.ofReal (finalGateMass p b g))⁻¹ ∂gateLaw M (l + 1) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (2 * M)) →
      ∃ f : ℝ → ℝ, IsDensity f ∧ SupportedInUnit f ∧
        outputLaw M (l + 1) b = densityLaw f ∧ AntitoneOn f (Set.Icc 0 1) ∧
        AbsolutelyContinuousOnInterval f 0 1 ∧
        ENNReal.ofReal (∫ x in (0 : ℝ)..1, |deriv f x|) =
          3 * ∫⁻ g, (ENNReal.ofReal (finalGateMass p b g))⁻¹ ∂gateLaw M (l + 1) ∧
        (∫ x in (0 : ℝ)..1, |deriv f x|) ≤ 3 * K * (2 : ℝ) ^ (2 * M) := by sorry

end BrickworkPorterThomas.Convergence
