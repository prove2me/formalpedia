-- Prove2me | Theorems.Thm_FermiHubbardMix_proposition_13_8
-- name    : FermiHubbardMix.proposition_13_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:29.76975+00:00
-- url     : https://prove2.me/theorems/550688a5-5e2f-410f-956a-ad61fe85c03f
-- title:
--   Proposition 13.8 — the coherent terms $C_B$ are quasi-local, $\|K^B_{i,r}\|\le6(6\zeta\beta)^r$
-- statement:
--   Let $H$ be a local fermionic Hamiltonian with onsite terms, $0<\beta\le1/(12\zeta)$, $i$ a site and $B\in\mathcal B_i$ a field-resonant jump. Then the coherent term (18) decomposes as
--   $$
--   C_B=\sum_{r\ge1}K^B_{i,r},\qquad \|K^B_{i,r}\|\le6(6\zeta\beta)^r,
--   $$
--   where each $K^B_{i,r}$ is even, Hermitian and supported on $\mathfrak B(\{i\},r)$. The sum starts at $r=1$: there is no onsite term.
--
--   The decomposition feeds the update matrix of the coherent step (Lemma 14.2).
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 13.2 assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 < β ≤ 1/(12ζ) → 0 < β and 12ζβ ≤ 1; reason: division-free form; the paper reads 1/0 as +∞, Lean's 1/0 = 0 would make the hypothesis false at ζ = 0
--   - encoding: C_B = ∑_{r≥1} K^B_{i,r} → HasSum (fun r => K (r+1)) C_B, bounds for every K r with 1 ≤ r; reason: the same series reindexed; K 0 is unused
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Proposition 13.8, p.62

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
import Definitions.Def_FermiHubbardMix_hgDist
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proposition 13.8 (Coherent terms are quasi-local)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.62). Let `0 < β ≤ 1/(12ζ)`, fix a
site `i` and a field-resonant jump `B ∈ B_i`. Then `C_B = ∑_{r ≥ 1} K^B_{i,r}` with
`‖K^B_{i,r}‖ ≤ 6(6ζβ)^r`, where each `K^B_{i,r}` is even, Hermitian and supported on `𝔅({i}, r)`.

**Formalization Note** `β ≤ 1/(12ζ)` is `12ζβ ≤ 1`. The sum starts at `r = 1`: it is
`∑_r K (r + 1)`, and `K 0` is unused. -/
theorem proposition_13_8 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (F : FRData ord H) (β : ℝ)
    (hβ : 0 < β) (hβζ : 12 * H.zeta * β ≤ 1) (i : Λ) (μ ν : LocCfg m) :
    ∃ K : ℕ → Op N,
      HasSum (fun r => K (r + 1))
        (cohTerm H.ham (F.jump i μ ν) β (F.sigma β i μ ν) (F.sigma β i μ ν) (F.delta β i μ ν)) ∧
      ∀ r, 1 ≤ r → opNorm (K r) ≤ 6 * (6 * H.zeta * β) ^ r ∧ IsEven (K r) ∧ (K r).IsHermitian ∧
        K r ∈ localAlg ord (hgBall H.edges {i} r) := by sorry

end FermiHubbardMix
