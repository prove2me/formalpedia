-- Prove2me | Theorems.Thm_BaconThesis_ExchangeUniv_eq_C_4
-- name    : BaconThesis.ExchangeUniv.eq_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:17.293979+00:00
-- url     : https://prove2.me/theorems/cfc79e3f-6fc5-45bd-bfdb-876aeae43474
-- title:
--   Eq. (C.4) (corrected: $\tfrac12(-E_{12}+E_{13}+E_{23})=\mathrm{diag}(\tfrac12,1,-1)$) — exchange combinations on the three-qubit DFS
-- statement:
--   On three qubits let
--   $$
--   A_1=\tfrac13(E_{12}+E_{13}+E_{23}),\qquad A_2=\tfrac12(-E_{12}+E_{13}+E_{23}),\qquad A_3=\tfrac1{\sqrt3}(E_{13}-E_{23}),
--   $$
--   and let $|\tfrac12,\lambda,\mu\rangle$ be the four states of (C.1). Then:
--
--   1. the four states $|\tfrac12,\lambda,\mu\rangle$ lie in the total-spin-$\tfrac12$ subspace;
--   2. on the total-spin-$\tfrac32$ subspace, $A_1=1$, $A_2=\tfrac12$ and $A_3=0$;
--   3. for $\mu=0,1$: $A_1|\tfrac12,\lambda,\mu\rangle=0$; $A_2|\tfrac12,0,\mu\rangle=|\tfrac12,0,\mu\rangle$ and $A_2|\tfrac12,1,\mu\rangle=-|\tfrac12,1,\mu\rangle$; $A_3|\tfrac12,0,\mu\rangle=|\tfrac12,1,\mu\rangle$ and $A_3|\tfrac12,1,\mu\rangle=|\tfrac12,0,\mu\rangle$.
--
--   In the basis $\{|\tfrac32,0\rangle,|\tfrac12,0\rangle,|\tfrac12,1\rangle\}$, acting on every $\mu$ at once, this reads
--   $$
--   A_1=\mathrm{diag}(1,0,0),\qquad A_2=\mathrm{diag}(\tfrac12,1,-1),\qquad A_3=\begin{pmatrix}0&0&0\\0&0&1\\0&1&0\end{pmatrix},
--   $$
--   so $A_2$ and $A_3$ act as $\sigma_z$ and $\sigma_x$ on $\mathrm{DFS}_3(\tfrac12)$.
--
--   The printed (C.4) gives $A_2=\mathrm{diag}(0,1,-1)$. Its first entry is $\tfrac12$: on $|111\rangle$, which has total spin $\tfrac32$, every $E_{ij}$ acts as $1$, so $A_2|111\rangle=\tfrac12(-1+1+1)|111\rangle$. This agrees with the book's own matrices (C.3). The $\mathrm{DFS}_3(\tfrac12)$ block, which is what the book uses, is as printed.
--
--   **Formalization Note** Qubits $1,2,3$ are $0,1,2$. The $J=\tfrac32$ rows are stated on the whole eigenspace of $(S^{[3]})^2$ for $\tfrac{15}4$.
--
--   Differences from the source:
--   - correction: (C.4) ½(−E12 + E13 + E23) = diag(0, 1, −1) → diag(1/2, 1, −1); reason: on |111⟩ = |3/2, 0, 3/2⟩ each E_ij is 1, so the (1,1) entry is ½(−1 + 1 + 1) = 1/2; (C.3) gives the same
--   - generalization: the J = 3/2 rows on the representative |111⟩ (μ = 3/2) → on the whole total-spin-3/2 subspace; reason: the page states the action does not depend on μ; specializes to |111⟩
--   - generalization: (C.1) uses the four states as J = 1/2 states → their membership in the total-spin-1/2 subspace is stated as a clause; reason: an extra true conclusion that makes the basis meaningful
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §C.1, eqs. (C.1)–(C.4), pp.245–246 (PDF pp.262–263)

import Mathlib
import Definitions.Def_BaconThesis_Collective_exchange
import Definitions.Def_BaconThesis_ExchangeUniv_dfsSpace
import Definitions.Def_BaconThesis_ExchangeUniv_ket3

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **(C.4), corrected: three linear combinations of exchanges on the `n = 3` DFS.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (C.1)–(C.4), pp.245–246 (PDF pp.262–263).

On three qubits let `A₁ = ⅓(E₁₂ + E₁₃ + E₂₃)`, `A₂ = ½(−E₁₂ + E₁₃ + E₂₃)` and
`A₃ = (E₁₃ − E₂₃)/√3`. In the basis `{|3/2, 0⟩, |1/2, 0⟩, |1/2, 1⟩}` (acting simultaneously on
every `μ`) they are `diag(1, 0, 0)`, `diag(1/2, 1, −1)` and `[[0,0,0],[0,0,1],[0,1,0]]`:
0. the four vectors `|1/2, λ, μ⟩` of (C.1) lie in the total-spin-`1/2` subspace;
1. on the total-spin-`3/2` subspace (every `|3/2, 0, μ⟩`), `A₁ = 1`, `A₂ = 1/2`, `A₃ = 0`;
2. for `μ = 0, 1`: `A₁|1/2, λ, μ⟩ = 0`, `A₂|1/2, 0, μ⟩ = |1/2, 0, μ⟩`, `A₂|1/2, 1, μ⟩ = −|1/2, 1, μ⟩`,
   `A₃|1/2, 0, μ⟩ = |1/2, 1, μ⟩`, `A₃|1/2, 1, μ⟩ = |1/2, 0, μ⟩`.

The printed (C.4) gives `A₂ = diag(0, 1, −1)`; its `(1,1)` entry is `1/2` (on `|111⟩` each `E_ij`
is `1`, so `A₂|111⟩ = ½(−1 + 1 + 1)|111⟩`), consistent with the book's own (C.3). The restriction
to `DFS₃(1/2)` — the book's "σ_z on DFS₃(1/2)" — is as printed.

**Formalization Note.** Qubits `1, 2, 3` are `0, 1, 2`, so `E₁₂, E₁₃, E₂₃` are `exchange 0 1`,
`exchange 0 2`, `exchange 1 2`. The `J = 3/2` rows are stated basis-free on `dfsSpace 3 (3/2)`. -/
theorem eq_C_4 :
    let E₁₂ := BaconThesis.Collective.exchange (n := 3) 0 1
    let E₁₃ := BaconThesis.Collective.exchange (n := 3) 0 2
    let E₂₃ := BaconThesis.Collective.exchange (n := 3) 1 2
    let A₁ := (1 / 3 : ℂ) • (E₁₂ + E₁₃ + E₂₃)
    let A₂ := (1 / 2 : ℂ) • (-E₁₂ + E₁₃ + E₂₃)
    let A₃ := ((1 / Real.sqrt 3 : ℝ) : ℂ) • (E₁₃ - E₂₃)
    (∀ lam mu : Fin 2, ket3 lam mu ∈ dfsSpace 3 (1 / 2)) ∧
    (∀ v ∈ dfsSpace 3 (3 / 2), A₁ *ᵥ v = v ∧ A₂ *ᵥ v = (1 / 2 : ℂ) • v ∧ A₃ *ᵥ v = 0) ∧
    (∀ mu : Fin 2,
      A₁ *ᵥ ket3 0 mu = 0 ∧ A₁ *ᵥ ket3 1 mu = 0 ∧
      A₂ *ᵥ ket3 0 mu = ket3 0 mu ∧ A₂ *ᵥ ket3 1 mu = -ket3 1 mu ∧
      A₃ *ᵥ ket3 0 mu = ket3 1 mu ∧ A₃ *ᵥ ket3 1 mu = ket3 0 mu) := by sorry

end BaconThesis.ExchangeUniv
