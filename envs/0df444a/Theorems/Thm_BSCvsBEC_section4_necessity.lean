-- Prove2me | Theorems.Thm_BSCvsBEC_section4_necessity
-- name    : BSCvsBEC.section4_necessity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:15.212914+00:00
-- url     : https://prove2.me/theorems/fb4ca07c-4aee-4c0c-bdb6-c51dd2807b5a
-- title:
--   §4 necessity: $H(X\mid\mathrm{PSC}_\theta(X))/H(X)\to\cos^2\theta$ for $X\sim\mathrm{Ber}(\epsilon)$, $\epsilon\to0$
-- statement:
--   Let $0\le\theta\le\pi/2$ and $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$. For a single input bit $X\sim\mathrm{Ber}(\epsilon)$ ($\Pr[X=1]=\epsilon$):
--   1. as $\epsilon\to0^+$,
--   $$\frac{H(X\mid\mathrm{PSC}_\theta(X))}{H(X)}\ \longrightarrow\ \cos^2\theta;$$
--   2. for every $\lambda\in[0,1]$ and $\epsilon\in[0,1]$, $H(X\mid\mathrm{BEC}_\lambda(X))=\lambda H(X)$.
--
--   Hence the constant $\cos^2\theta$ in Theorem 1.3 cannot be lowered, already for one biased bit.
--
--   Differences from the source:
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ; reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: ε → 0 → ε → 0⁺ (the filter 𝓝[>] 0); reason: Ber(ε) is defined for ε ∈ [0, 1] and the ratio is 0/0 at ε = 0
--   - encoding: X ∼ Ber(ε), a single bit → the pmf on Fin 1 → Fin 2 with mass ε on 1 and 1 − ε on 0; reason: n = 1 in the n-fold definitions; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §4, p.19 (after Theorem 4.1)

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_condEntBEC
import Definitions.Def_BSCvsBEC_condEntPSC

open Filter Topology

namespace BSCvsBEC

/-- **§4, p.19 (necessity of the constant).** For a single input bit `X ∼ Ber(ε)`,
`H(X | PSC_θ(X)) / H(X) → cos²θ` as `ε → 0⁺`, whereas `H(X | BEC_λ(X)) = λ H(X)`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), §4, p.19: "The constant is necessary already for a single biased input bit: if `X ∼ Ber(ε)` and
`ε → 0`, then `H(X | PSC_θ(X))/H(X) → cos²θ`, whereas `H(X | BEC_λ(X)) = λH(X)`."

**Formalization Note.** `n = 1`; `Ber(ε)` is the pmf on `Fin 1 → Fin 2` with mass `ε` on the input
`1` and `1 − ε` on `0`. The limit is one-sided (`ε > 0`, where `H(X) > 0`); the BEC identity is
stated for every `ε ∈ [0, 1]` and `λ ∈ [0, 1]`. -/
theorem section4_necessity (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : IsPSCPair θ ω) :
    Tendsto
        (fun ε : ℝ =>
          condEntPSC ω (fun x : Fin 1 → Fin 2 => if x 0 = 1 then ε else 1 - ε) /
            shannon (fun x : Fin 1 → Fin 2 => if x 0 = 1 then ε else 1 - ε))
        (𝓝[>] 0) (𝓝 (Real.cos θ ^ 2)) ∧
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        condEntBEC lam (fun x : Fin 1 → Fin 2 => if x 0 = 1 then ε else 1 - ε) =
          lam * shannon (fun x : Fin 1 → Fin 2 => if x 0 = 1 then ε else 1 - ε) := by sorry

end BSCvsBEC
