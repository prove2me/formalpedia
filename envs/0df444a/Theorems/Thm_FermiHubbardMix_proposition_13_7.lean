-- Prove2me | Theorems.Thm_FermiHubbardMix_proposition_13_7
-- name    : FermiHubbardMix.proposition_13_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:52.122914+00:00
-- url     : https://prove2.me/theorems/2c88a55e-3e00-42f2-9e00-11f8942ef8a3
-- title:
--   Proposition 13.7 — the field-resonant jumps $A_B(\omega)$ are quasi-local
-- statement:
--   Let $H$ be a local fermionic Hamiltonian with onsite terms, $0<\beta\le1/(4\zeta)$, $i$ a site and $B\in\mathcal B_i$ a field-resonant jump. Then the jump operator (17) decomposes as
--   $$
--   A_B(\omega)=\sum_{r\ge0}G^{B,\omega}_{i,r},\qquad \|G^{B,\omega}_{i,r}\|\le(2\pi)^{-1/4}\sigma_B^{-1/2}\bigl(2\zeta\sigma_B^{-1}\bigr)^r,
--   $$
--   where each $G^{B,\omega}_{i,r}$ is homogeneous with the parity of $B$ and supported on $\mathfrak B(\{i\},r)$, and
--   $$
--   G^{B,\omega}_{i,0}=\frac1{\sqrt{2\pi}}\int_{-\infty}^{\infty}e^{itv_i}Be^{-itv_i}e^{-i\omega t}f_B(t)\,dt.\tag{22}
--   $$
--   The decomposition feeds the update matrix of the dissipative step (Lemma 14.3).
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 13.2 assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 < β ≤ 1/(4ζ) → 0 < β and 4ζβ ≤ 1; reason: division-free form; the paper reads 1/0 as +∞, Lean's 1/0 = 0 would make the hypothesis false at ζ = 0
--   - generalization: A_B(ω) admits a decomposition (for each ω) → a decomposition G : ℕ → ℝ → Op with each G_r continuous in ω; reason: the paper's shells are Fourier transforms of integrable functions, hence continuous; Lemma 14.3 integrates them in ω
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Proposition 13.7, p.62, eq. (22)

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_hgDist
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proposition 13.7 (Jump operators are quasi-local)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.62). Let `0 < β ≤ 1/(4ζ)`, fix a
site `i` and a field-resonant jump `B ∈ B_i`. Then `A_B(ω) = ∑_{r ≥ 0} G^{B,ω}_{i,r}` with
`‖G^{B,ω}_{i,r}‖ ≤ (2π)^{-1/4} σ_B^{-1/2} (2ζσ_B^{-1})^r`, where `G^{B,ω}_{i,r}` is homogeneous with
the parity of `B` and supported on `𝔅({i}, r)`, and `G^{B,ω}_{i,0}` is eq. (22).

**Formalization Note** `β ≤ 1/(4ζ)` is `4ζβ ≤ 1` (no condition when `ζ = 0`, as in the paper). The
field-resonant jumps are `U_i† P^i_{µν} U_i` (`FRData.jump`). The decomposition is a function of
`ω`, each `G_r` continuous in `ω`. -/
theorem proposition_13_7 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (F : FRData ord H) (β : ℝ)
    (hβ : 0 < β) (hβζ : 4 * H.zeta * β ≤ 1) (i : Λ) (μ ν : LocCfg m) :
    ∃ G : ℕ → ℝ → Op N, (∀ r, Continuous (G r)) ∧
      (∀ ω, HasSum (fun r => G r ω) (jumpOp H.ham (F.jump i μ ν) (F.sigma β i μ ν) ω)) ∧
      (∀ r ω, opNorm (G r ω) ≤ (2 * Real.pi) ^ (-(1 / 4 : ℝ)) * F.sigma β i μ ν ^ (-(1 / 2 : ℝ)) *
        (2 * H.zeta / F.sigma β i μ ν) ^ r) ∧
      (∀ r ω, (IsEven (F.jump i μ ν) → IsEven (G r ω)) ∧ (IsOdd (F.jump i μ ν) → IsOdd (G r ω))) ∧
      (∀ r ω, G r ω ∈ localAlg ord (hgBall H.edges {i} r)) ∧
      (∀ ω, G 0 ω = jumpOp (H.v i) (F.jump i μ ν) (F.sigma β i μ ν) ω) := by sorry

end FermiHubbardMix
