-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_3_3
-- name    : DQILocal.Recon.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:28:01.259271+00:00
-- url     : https://prove2.me/theorems/410c4f63-8952-4b73-a933-d1a9ae451cc2
-- title:
--   Theorem 3.3, p. 17 — output guarantees of Regev's reduction: expected TV distance $\le\sqrt\varepsilon$, bounded averages within $2\sqrt\varepsilon$
-- statement:
--   Let $q\ge2$, let $B$ be a 0/1 matrix with $m$ rows over $\mathbb Z_q$, $K=\{Bz\}$, and let $\Phi$ be an amplitude function. Let a coherent decoder for the decoding problem with amplitude function $\Phi$ have block success $1-\varepsilon$ with $\varepsilon<1$, and let $\nu_{x_0}$ be the law of the violation pattern that Regev's reduction outputs when it uses this decoder with offset $x_0$, where $x_0$ is uniform on $\mathbb Z_q^m$.
--
--   1. If $\Phi$ has positive mass $\sum_{x\in X}|\Phi(x)|^2$ on every coset $X$ of $K$, and $\pi^\Phi_{x_0}(x)\propto|\Phi(x)|^2$ on $x_0+K$, then
--   $$\mathbb E_{x_0}\,\|\nu_{x_0}-\pi^\Phi_{x_0}\|_{\mathrm{TV}}\le\sqrt\varepsilon .$$
--   2. For every function $h:\mathbb Z_q^m\to[0,1]$,
--   $$\Bigl|\mathbb E_{x_0}\mathbb E_{x\sim\nu_{x_0}}h(x)-\sum_{x\in\mathbb Z_q^m}|\Phi(x)|^2h(x)\Bigr|\le2\sqrt\varepsilon .$$
--
--   This translates the success of a decoder into a guarantee on the output of DQI: the output law is close to the target law on average over the offset, and averages of bounded functions are close to their values in the state $|\Phi\rangle$. Part 2 needs no assumption on the coset masses.
--
--   **Formalization Note** The code is over $\mathbb Z_q$ for every $q\ge2$, so $C$ need not be a free module. The output law is built step by step from the procedure (prepare, apply $U$, check, renormalize, subtract the outcome, apply $U^\dagger$, measure, replace patterns outside $x_0+K$ by $x_0$).
--
--   Differences from the source:
--   - encoding: "a decoder", run coherently by Regev's reduction → a coherent decoder (finite work type, initial work state, outcome map, unitary); its block success and local estimate are those of the POVM it induces; reason: Regev's reduction applies the decoder as a unitary dilation (proof of Theorem 3.3, p. 17); every POVM is induced by some coherent decoder
--   - encoding: "the law of the violation pattern that Regev's reduction outputs" → regevLaw: the post-check state after the uncomputation, measured on the received register, with patterns outside x0 + K sent to x0; reason: the procedure of p. 17 written as explicit linear maps; restarts do not change the output law
--   - encoding: every coset X of K → every coset x0 + K with x0 ∈ Z_q^m; reason: the same cosets
--   - encoding: checks indexed by [n] → checks indexed by any finite type; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 3.3, p. 17; proof pp. 17–18

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_Amplitude
import Definitions.Def_DQILocal_Recon_Supplement_Regev

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon

/-- **Theorem 3.3 (Output guarantees).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 3.3, p. 17.
"Let `q ≥ 2` and let `Φ` be an amplitude function. Suppose that a decoder for the decoding problem
with amplitude function `Φ` has block success `1 - ε` with `ε < 1`. Let `x₀` be uniformly distributed
on `ℤ_q^m`, and let `ν_{x₀}` be the law of the violation pattern that Regev's reduction outputs when
it uses this decoder.
1. Suppose that `Φ` has positive mass `Σ_{x∈X} |Φ(x)|²` on every coset `X` of `K`, and let
   `π^Φ_{x₀}(x) ∝ |Φ(x)|²` on `x₀ + K`. Then `E_{x₀} ‖ν_{x₀} - π^Φ_{x₀}‖_TV ≤ √ε`.
2. For every function `h : ℤ_q^m → [0, 1]`,
   `|E_{x₀} E_{x∼ν_{x₀}} h(x) - Σ_x |Φ(x)|² h(x)| ≤ 2√ε`."

**Formalization Note.** The decoder is a coherent decoder (finite work type `W`, initial work state,
outcome map, unitary `U`), because Regev's reduction runs it coherently (p. 16–17); its block success
is that of its induced POVM (Definition 3.2). `ν_{x₀}` is `regevLaw`, built step by step from the
procedure of p. 17. Every coset of `K` is `x₀ + K` for some `x₀`. The code is over `ℤ_q` for every
`q ≥ 2` (not only prime `q`); `B` is any 0/1 matrix with any finite check type. -/
theorem theorem_3_3 (q : ℕ) [NeZero q] (hq : 2 ≤ q) {m : ℕ} {κ : Type} [Fintype κ]
    (B : Matrix (Fin m) κ Bool) (Φ : (Fin m → ZMod q) → ℂ) (hΦ : IsAmplitude Φ)
    {W : Type} [Fintype W] [DecidableEq W] (Dec : CoherentDecoder q m W) (ε : ℝ) (hε : ε < 1)
    (hs : blockSuccessGen Φ B (inducedPOVM Dec) = 1 - ε) :
    ((∀ x₀ : Fin m → ZMod q, 0 < cosetMass B Φ x₀) →
      offsetAvg (fun x₀ => tvDist (regevLaw Φ B Dec x₀) (targetLaw B Φ x₀)) ≤ Real.sqrt ε) ∧
    (∀ h : (Fin m → ZMod q) → ℝ, (∀ x, 0 ≤ h x ∧ h x ≤ 1) →
      |regevExpect Φ B Dec h - ∑ x, ‖Φ x‖ ^ 2 * h x| ≤ 2 * Real.sqrt ε) := by sorry

end DQILocal.Recon.Supplement
