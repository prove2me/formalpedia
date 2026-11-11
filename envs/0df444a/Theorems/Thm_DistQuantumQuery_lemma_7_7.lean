-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_7_7
-- name    : DistQuantumQuery.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:25.715639+00:00
-- url     : https://prove2.me/theorems/09019541-6509-4ea1-b5a9-2693d28af04c
-- title:
--   Lemma 7.7 — $\|E^\uparrow_\Gamma(X)\circ\Delta_{ij}\|\le\|X\circ\Delta_i\|\cdot\|\Gamma\circ\Delta_j\|$
-- statement:
--   Let $g:\Sigma_g\to\{0,1\}$ be a decision problem on $\Sigma_g\subseteq\{0,1\}^m$ and $\Gamma\in L(\Sigma_g)$ real symmetric with $\|\Gamma\|\le1$ and $\Gamma\circ\Delta_g=\Gamma$. Then for every $X\in\mathrm{Herm}(\{0,1\}^n)$, $i\in[n]$ and $j\in[m]$,
--   $$
--   \|E^\uparrow_\Gamma(X)\circ\Delta_{ij}\|\le\|X\circ\Delta_i\|\cdot\|\Gamma\circ\Delta_j\| ,
--   $$
--   where $\Delta_{ij}$ is the query filter of bit $j$ of block $i$ of a composed input.
--
--   This bounds the filtered norms of the lifted certificate in the composition proof.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: {0,1}^n and Σ_g^n with n blocks, positions (i, j) → ι → Bool and ι → Σ_g, positions ι × κ; reason: relabelling blocks and inner positions
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 7.7, p.61

import Mathlib
import Definitions.Def_DistQuantumQuery_traceNorm
import Definitions.Def_DistQuantumQuery_muMat
import Definitions.Def_DistQuantumQuery_liftUp

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 7.7** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 7.7, p.61). Let `g : Σ_g → {0,1}` be a decision problem on
`Σ_g ⊆ {0,1}^m` and `Γ ∈ L(Σ_g)` real symmetric with `‖Γ‖ ≤ 1` and `Γ ∘ Δ_g = Γ`. Then for every
`X ∈ Herm({0,1}^n)`, `i ∈ [n]` and `j ∈ [m]`, `‖E↑_Γ(X) ∘ Δ_{ij}‖ ≤ ‖X ∘ Δ_i‖ · ‖Γ ∘ Δ_j‖`.

**Formalization Note** `Δ_{ij}` on `Σ_g^n` is the filter of bit `j` of block `i`
(`qfilt innerBits (i, j)`); `Δ_i` on `{0,1}^n` is `qfilt id i`; `Δ_j` on `Σ_g` is `qfilters Σ_g j`. -/
theorem lemma_7_7 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Sg : Finset (κ → Bool)) (g : Sg → Bool) (Γ : Matrix Sg Sg ℂ) (hΓreal : ∀ x y, (Γ x y).im = 0) (hΓsymm : Γᵀ = Γ)
    (hΓnorm : opNorm Γ ≤ 1) (hΓg : Γ ⊙ disagree g = Γ)
    (X : Matrix (ι → Bool) (ι → Bool) ℂ) (hX : X.IsHermitian) (i : ι) (j : κ) :
    opNorm (liftUp g Γ X ⊙ qfilt (fun x : ι → Sg => innerBits x) (i, j)) ≤
      opNorm (X ⊙ qfilt (fun x : ι → Bool => x) i) * opNorm (Γ ⊙ qfilters Sg j) := by sorry

end DistQuantumQuery
