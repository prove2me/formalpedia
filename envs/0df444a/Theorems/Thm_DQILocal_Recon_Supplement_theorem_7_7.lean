-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_7_7
-- name    : DQILocal.Recon.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:03:57.866762+00:00
-- url     : https://prove2.me/theorems/53c10bbc-9906-42bf-a04c-78d3fd562731
-- title:
--   Theorem 7.7, p. 62 — below $\beta_c$ the PGM succeeds, above $\beta_c$ every decoder has block success at most $e^{-\varepsilon m}$
-- statement:
--   Let $q=2$, $f(z)=z$, $k\ge3$ and $k<D$, and let $B$ be drawn from the configuration model, with or without the conditioning on the absence of multiple edges.
--
--   1. If $0\le\beta<\beta_c$, then
--   $$\mathbb E_B\bigl[1-P_{\mathrm{PGM}}(B,\beta)\bigr]\to0\qquad(m\to\infty);$$
--   in particular, for every $\delta>0$, $\Pr_B[P_{\mathrm{PGM}}(B,\beta)<1-\delta]\to0$.
--   2. If $\beta>\beta_c$, then there are $\varepsilon>0$ and $c>0$ such that, for all large $m$, with probability at least $1-e^{-cm}$ over the instance, every decoder for the decoding problem induced by DQI with $\Phi_\beta$ has block success at most $e^{-\varepsilon m}$.
--
--   The condensation threshold $\beta_c$ thus separates the inverse temperatures at which an optimal decoder succeeds from those at which every decoder fails exponentially.
--
--   **Formalization Note** Limits are along $m$ with $D\mid km$. A decoder is any POVM on the $m$ received qubits with outcomes in $\mathbb Z_2^m$.
--
--   Differences from the source:
--   - reading: "with probability 1 − e^{−Ω(m)}" → there is c > 0 such that, for all large admissible m, the probability is at least 1 − e^{−cm}; reason: the standard meaning of Ω(m); the constants may depend on the law of B, which the theorem fixes
--   - encoding: a decoder (a measurement, possibly with ancillas) → a POVM on the received qudits with outcomes in Z_q^m; reason: Naimark dilation: the two describe the same outcome laws
--   - encoding: "block success 1 − o(1) with probability 1 − o(1)" → for every δ > 0, Pr_B[P_PGM(B, β) < 1 − δ] → 0; reason: the definition of o(1)
--   - encoding: F_B(α) = Σ_X W_{B,α}(X) ln(|C| W_{B,α}(X)) and F̄ = lim (1/n) E_B F_B → Σ_e Pr[E = e] ln(|C| W_{B,α}(e + K)) and limUnder along admissible m; reason: grouping the terms of each coset; the limit exists by Proposition 7.6(3)
--   - encoding: m → ∞ → m → ∞ along admissible m (D ∣ km); reason: the model exists only for admissible m
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 7.7, p. 62; definitions pp. 56–57, 60–61

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_ConfigModel
import Definitions.Def_DQILocal_Recon_Supplement_Condensation

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon Filter Topology

/-- **Theorem 7.7 (The optimal decoder and the condensation threshold).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 7.7, p. 62.
"Let `q = 2`, `f(z) = z`, `k ≥ 3`, and `k < D`, and let `B` be drawn from the configuration model,
with or without the conditioning on the absence of multiple edges.
(a) If `0 ≤ β < β_c`, then `E_B[1 - P_PGM(B, β)] → 0` as `m → ∞`. In particular, the PGM has block
success `1 - o(1)` with probability `1 - o(1)` over the instance.
(b) If `β > β_c`, then there is `ε > 0` such that, with probability `1 - e^{-Ω(m)}` over the
instance, every decoder for the decoding problem induced by DQI with `Φ_β` has block success at most
`e^{-εm}`."

**Formalization Note.**
* `L = pairing` is the model without the conditioning (multigraph reduced modulo two, p. 60),
  `L = simple` the conditioned one; `m → ∞` along admissible `m` (`D ∣ km`).
* `β_c = ln((1 - α_c)/α_c)` with `α_c = sup{α ∈ (0, ½) : F̄(α) > 0}` and `F̄` the limit of
  `(1/n) E_B F_B(α)` in the unconditioned model (p. 61), `betaC`.
* `P_PGM(B, β)` is the block success of the pretty-good measurement itself (`PPGM`).
* "with probability `1 - o(1)`, block success `1 - o(1)`" is: for every `δ > 0`,
  `Pr_B[P_PGM(B, β) < 1 - δ] → 0`.
* "with probability `1 - e^{-Ω(m)}`" is read as: there is `c > 0` such that, for all large
  admissible `m`, the probability is at least `1 - e^{-cm}`.
* "every decoder" is every POVM on the `m` received qubits with outcomes in `ℤ_2^m` (Definition 3.2;
  ancillas absorbed by Naimark), and its block success is the base `blockSuccess` at `p_β`. -/
theorem theorem_7_7 (k D : ℕ) (hk : 3 ≤ k) (hkD : k < D) (L : CfgLaw) :
    (∀ β : ℝ, 0 ≤ β → β < betaC k D →
      Tendsto (fun m => cfgExpect L k D m (fun B => 1 - PPGM B β)) (admissible k D) (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun m => cfgProb L k D m (fun B => PPGM B β < 1 - δ)) (admissible k D) (𝓝 0)) ∧
    (∀ β : ℝ, betaC k D < β → ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in admissible k D,
        1 - Real.exp (-c * (m : ℝ)) ≤ cfgProb L k D m (fun B =>
          ∀ F : (Fin m → ZMod 2) → Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ, IsPOVM F →
            blockSuccess (gibbsWeight 2 fXor β) B F ≤ Real.exp (-ε * (m : ℝ)))) := by sorry

end DQILocal.Recon.Supplement
