-- Prove2me | Theorems.Thm_FermiHubbardMix_theorem_15_1
-- name    : FermiHubbardMix.theorem_15_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:12.341973+00:00
-- url     : https://prove2.me/theorems/2c3adf56-0c38-466e-9d2d-6db487fe04ad
-- title:
--   Theorem 15.1 — rapid mixing $\|e^{t\mathcal L_{\mathrm{FR}}}(\rho)-\sigma\|_1\le\varepsilon$ for $t\ge2\log(4n/\varepsilon)$, arbitrary onsite terms
-- statement:
--   Let $H=V+W$ be a local fermionic Hamiltonian on $n$ sites, each carrying $m$ complex fermionic modes, where $W$ has bounded $L$-site degree-$D$ couplings and the onsite part $V=\sum_iv_i$ is arbitrary. For every inverse temperature
--   $$
--   0<\beta\le4^{-m}(DL)^{-3}/9600,
--   $$
--   let $\sigma=e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$ and let $\mathcal L_{\mathrm{FR}}$ be the field-resonant Lindbladian of $H$ at $\beta$. Then for every fermionic density operator $\rho$, every $\varepsilon\in(0,1]$ and every $t\ge2\log(4n/\varepsilon)$,
--   $$
--   \bigl\|e^{t\mathcal L_{\mathrm{FR}}}(\rho)-\sigma\bigr\|_1\le\varepsilon .
--   $$
--   The temperature threshold and the mixing time do not depend on the onsite terms.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - reading: L_FR of H for arbitrary onsite part V (Definition 13.4 through Remark 13.3) → L_FR built from any onsite eigenbasis F : FRData (even unitaries U_i diagonalizing v_i), for every such F; reason: Remark 13.3 chooses some U_i and the theorem holds for whichever is chosen; the conjugation is made explicit
--   - encoding: 0 < β ≤ 4^{-m}(DL)^{-3}/9600 → 0 < β and 9600·4^m(DL)³β ≤ 1; reason: division-free form of the same condition
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 15.1, p.68

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_semigroup
import Definitions.Def_FermiHubbardMix_gibbs
import Definitions.Def_WildeQIT_traceNorm
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Theorem 15.1 (Rapid mixing for fermionic Gibbs states with arbitrary onsite terms)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…),
p.68). Let `H = V + W` be a local fermionic Hamiltonian on `n` sites, each carrying `m` complex
fermionic modes, where `W` has bounded `L`-site degree-`D` couplings and the onsite part is
arbitrary. For `0 < β ≤ 4^{-m}(DL)^{-3}/9600`, let `σ = e^{-βH}/tr(e^{-βH})` and `L_FR` the
field-resonant Lindbladian of `H` at `β`. Then for every fermionic density operator `ρ`, every
`ε ∈ (0, 1]` and every `t ≥ 2 log(4n/ε)`, `‖e^{tL_FR}(ρ) - σ‖₁ ≤ ε`.

**Formalization Note** The threshold is `9600·4^m(DL)³β ≤ 1`. The onsite terms are arbitrary: the
field-resonant Lindbladian is built from any onsite eigenbasis `F : FRData` (Remark 13.3), and the
statement holds for every one of them and every mode ordering `ord`. -/
theorem theorem_15_1 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (L D : ℕ)
    (hLD : H.BoundedCouplings L D) (β : ℝ) (hβ : 0 < β)
    (hβLD : 9600 * 4 ^ m * ((D : ℝ) * L) ^ 3 * β ≤ 1) (F : FRData ord H) (ρ : Op N)
    (hρ : IsDensity ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ)
    (ht : 2 * Real.log (4 * Fintype.card Λ / ε) ≤ t) :
    WildeQIT.traceNorm (semigroup (lindFR ord H F β) t ρ - gibbs β H.ham) ≤ ε := by sorry

end FermiHubbardMix
