-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_4_6
-- name    : DistQuantumQuery.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:53.258038+00:00
-- url     : https://prove2.me/theorems/d9c453b7-bda0-46f4-81b1-a27b02e0114c
-- title:
--   Lemma 4.6 — one-query decomposition $\Psi_{t-1}-\Psi_t=2\sum_i\Delta_i\circ Z^t_i$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$ and let $Q$ be a $T$-query algorithm. For $t\in[0:T]$ let $\Psi_t(x,y)=\langle\psi^t_x|\psi^t_y\rangle$ be its Gram matrix after $t$ queries, where $|\psi^0_x\rangle=U_0|0\rangle$ and $|\psi^t_x\rangle=U_tO_x|\psi^{t-1}_x\rangle$. Then for every $t\in[T]$ there is a decomposition $\Psi_{t-1}=\sum_{i=0}^nZ^t_i$ with all $Z^t_i\succeq0$ such that
--   $$
--   \Psi_{t-1}-\Psi_t=2\sum_{i=1}^n\Delta_i\circ Z^t_i .
--   $$
--   This one-query step drives the hybrid argument behind the $\bar\gamma_2$ lower bound (Proposition 4.7).
--
--   **Formalization Note** The index $i=0$ is the null index `none`; $i\in[n]$ is `some i`.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 4.6, p.40

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 4.6 (One-query decomposition)** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 4.6, p.40).
Let `Q` be a `T`-query algorithm and `Ψ_t(x, y) = ⟨ψ^t_x|ψ^t_y⟩` its Gram matrix after `t`
queries, `|ψ^0_x⟩ = U_0|0⟩`, `|ψ^t_x⟩ = U_t O_x |ψ^{t−1}_x⟩`. For every `t ∈ [T]` there is a PSD
decomposition `Ψ_{t−1} = Σ_{i=0}^n Z^t_i`, `Z^t_i ⪰ 0`, with `Ψ_{t−1} − Ψ_t = 2 Σ_{i=1}^n Δ_i ∘ Z^t_i`.

**Formalization Note** The index `i = 0` is `none : Option ι`; `i ∈ [n]` is `some i`. The
algorithm has ancilla `Fin (d + 1)` and starts from `startVec`. -/
theorem lemma_4_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool)) {d T : ℕ}
    (A : QueryAlg ι (d + 1) T) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    ∃ Z : Option ι → Matrix S S ℂ, (∀ i, (Z i).PosSemidef) ∧
      gram (fun x : S => A.stateFrom x.1 (startVec ι d) (t - 1)) = ∑ i, Z i ∧
      gram (fun x : S => A.stateFrom x.1 (startVec ι d) (t - 1)) -
          gram (fun x : S => A.stateFrom x.1 (startVec ι d) t) =
        (2 : ℂ) • ∑ i : ι, qfilters S i ⊙ Z (some i) := by sorry

end DistQuantumQuery
