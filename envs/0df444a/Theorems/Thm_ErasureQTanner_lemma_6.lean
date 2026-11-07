-- Prove2me | Theorems.Thm_ErasureQTanner_lemma_6
-- name    : ErasureQTanner.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:49.475433+00:00
-- url     : https://prove2.me/theorems/c5229bb4-f677-4d37-80d3-81e88a53cd3c
-- title:
--   Lemma 6 — correlating erasures can only raise the expected covered dimension
-- statement:
--   Let $C\subseteq\mathbb F_q^n$ be a linear code, $T\subseteq[n]$, $\{A_1,\dots,A_t\}$ a partition of $T$, $\rho\in[0,1]$, and let $\mu$ be the law on $\{0,1\}^T$ that sets $x_{A_i}$ to all ones with probability $\rho$ and to all zeros otherwise, independently for each $i$. Then for every pattern on $[n]\setminus T$,
--   $$\mathop{\mathbb E}_{x_T\sim\rho}[\dim S_C(x)]\le\mathop{\mathbb E}_{x_T\sim\mu}[\dim S_C(x)].$$
--   This is the technical tool behind the tensor theorem: a tensor code is easy to analyse under column-correlated erasures.
--
--   Differences from the source:
--   - encoding: a partition $\{A_1,\dots,A_t\}$ of $T$ → a labelling $T\to\{1,\dots,t\}$, parts possibly empty; reason: every partition is such a labelling; an empty part only adds a coin that changes nothing
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Lemma 6, p.15

import Mathlib
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered

set_option autoImplicit false

namespace ErasureQTanner

/-- **Lemma 6.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.15: for every field `F_q`, every `T ⊆ [n]` and partition `{A₁,…,A_t}` of `T`, every `ρ ∈ [0, 1]`,
partial pattern and linear code, `E_{x_T∼ρ}[dim S_C(x)] ≤ E_{x_T∼µ}[dim S_C(x)]`, where `µ` erases each part as a whole.

**Formalization Note.** The partition is the map `label : T → Fin t`, with `A_j = label⁻¹(j)`; this covers every partition of
`T` and also allows empty parts, where the coin of the part does nothing. `x₀` carries the partial pattern; only its values
outside `T` are read. -/
theorem lemma_6 {F : Type*} [Field F] [Fintype F] {n t : ℕ} (T : Finset (Fin n))
    (label : {i // i ∈ T} → Fin t) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x₀ : Fin n → Bool)
    (C : Submodule F (Fin n → F)) :
    noisyExp ρ (fun y : {i // i ∈ T} → Bool =>
        (Module.finrank F (covered C fun i => if h : i ∈ T then y ⟨i, h⟩ else x₀ i) : ℝ)) ≤
      noisyExp ρ (fun z : Fin t → Bool =>
        (Module.finrank F (covered C fun i => if h : i ∈ T then z (label ⟨i, h⟩) else x₀ i) : ℝ)) := by sorry

end ErasureQTanner
