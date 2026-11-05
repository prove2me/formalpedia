-- Prove2me | Theorems.Thm_DHRUniq_concentration_dilution
-- name    : DHRUniq.concentration_dilution
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:37.177211+00:00
-- url     : https://prove2.me/theorems/68efca61-3251-4e1b-9192-8eb301d93f2b
-- title:
--   Displays (37-a), (37-b): exact concentration and dilution of $\phi_n$
-- statement:
--   Let $|\psi\rangle$ be a wavefunction on $\mathcal H^A\otimes\mathcal H^B$ with $S=S_{\mathrm{vN}}(|\psi\rangle\langle\psi|)$, and let $0<\epsilon<\min\{S/2,1/2\}$. Then there is $N$ such that the following holds for all $n\ge N$. Let $|\psi^{\otimes n}\rangle=\sum_i\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle$ be a Schmidt decomposition and let $\mathrm{TYP}$ be an index set with
--
--   1. $2^{-n(S+\epsilon)}\le p_i\le2^{-n(S-\epsilon)}$ for $i\in\mathrm{TYP}$,
--   2. $p=\sum_{i\in\mathrm{TYP}}p_i\ge1-\epsilon$,
--   3. $\#\mathrm{TYP}\le2^{n(S+\epsilon)}$.
--
--   Put $|\phi_n\rangle=p^{-1/2}\sum_{i\in\mathrm{TYP}}\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle$. Then there are integers $a,b$, representatives $P_+^a$ of $P_+(\mathbb C^a)$ and $P_+^b$ of $P_+(\mathbb C^b)$ on $(\mathcal H^A)^{\otimes n}\otimes(\mathcal H^B)^{\otimes n}$, and LQCC operations $\Lambda_n,\Lambda_n'$ with
--
--   $$
--   \Lambda_n(|\phi_n\rangle\langle\phi_n|)=P_+^a,\quad\Big|\frac{\log_2a}{n}-S\Big|<\epsilon+\frac2n,
--   $$
--
--   $$
--   \Lambda_n'(P_+^b)=|\phi_n\rangle\langle\phi_n|,\quad\Big|\frac{\log_2b}{n}-S\Big|<\epsilon+\frac1n.
--   $$
--
--   These conversions connect the typical part of $n$ copies of $\psi$ to maximally entangled states with about $2^{nS}$ terms, which pins the regularization to $S$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - generalization: completely positive maps Λ_n and Λ′_n → LQCC operations; reason: LQCC operations are completely positive, and they are what the paper's proof provides and what (P2) needs
--   - generalization: H^A ≡ H^B ≡ H, and the decomposition and TYP chosen in the proof → ψ on any a × b, and every Schmidt decomposition and every TYP with (34-a,b,c), with N chosen before them; reason: the proof's choice is one instance; the existence of TYP (the AEP, posed elsewhere on the platform) is not part of the statement
--   - encoding: bases (e_i), (f_i) of H^⊗n → orthonormal families in IsSchmidtDecomp; reason: a basis is such a family
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §8, displays (34), (37-a), (37-b), pp. 18–19

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_IsSchmidtDecomp
import Definitions.Def_DHRUniq_IsMaxEntRep
import Definitions.Def_DHRUniq_IsLQCC
import Definitions.Def_DHRUniq_truncatedState
import Definitions.Def_WildeQIT_EntManip_entEntropy
import Definitions.Def_WildeQIT_EntManip_tensorPowVec
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT.EntManip (entEntropy tensorPowVec)

namespace DHRUniq

/-- **Displays (37-a), (37-b)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §8, pp. 18–19). Let `|ψ⟩` be a wavefunction with
`S = S_vN(|ψ⟩⟨ψ|)`. For `ε < min{S/2, 1/2}` and `n` sufficiently large there are maps `Λ_n`, `Λ′_n`
with `Λ_n(|φ_n⟩⟨φ_n|) = P_+^a` for a representative `P_+^a` of `P_+(ℂ^a)` in `H_tot` with
`|log_2 a / n − S| < ε + 2/n`, and `Λ′_n(P_+^b) = |φ_n⟩⟨φ_n|` for a representative `P_+^b` of
`P_+(ℂ^b)` in `H_tot` with `|log_2 b / n − S| < ε + 1/n`. Here `|φ_n⟩` is the truncation of a Schmidt
decomposition `|ψ^{⊗n}⟩ = ∑_i √p_i |e_i⟩ ⊗ |f_i⟩` to a set `TYP` with
(34-a) `2^{−n(S+ε)} ≤ p_i ≤ 2^{−n(S−ε)}` on `TYP`, (34-b) `p = ∑_{TYP} p_i ≥ 1 − ε`,
(34-c) `#TYP ≤ 2^{n(S+ε)}`.

**Formalization Note** `N` is chosen before the Schmidt data, and the claim holds for every Schmidt
data and every `TYP` satisfying (34); the existence of such a `TYP` is the asymptotic equipartition
theorem, not part of this statement. The paper's "completely positive maps" are stated as LQCC
operations, which is what its proof produces. `a` and `b` are existential, as printed. `ψ` lives on
any `a × b`, not only `H ⊗ H`. `H_tot` is `(Fin n → a) × (Fin n → b)`. -/
theorem concentration_dilution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ : a × b → ℂ) (hψ : IsUnitVec ψ) (ε : ℝ) (hε : 0 < ε)
    (hεS : ε < min (entEntropy ψ / 2) (1 / 2)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
      (e : ι → (Fin n → a) → ℂ) (f : ι → (Fin n → b) → ℂ) (TYP : Finset ι),
      IsSchmidtDecomp (tensorPowVec ψ n) p e f →
      (∀ i ∈ TYP, (2 : ℝ) ^ (-((n : ℝ) * (entEntropy ψ + ε))) ≤ p i ∧
        p i ≤ (2 : ℝ) ^ (-((n : ℝ) * (entEntropy ψ - ε)))) →
      1 - ε ≤ ∑ i ∈ TYP, p i →
      (TYP.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (entEntropy ψ + ε)) →
      ∃ (da db : ℕ) (Pa Pb : (Fin n → a) × (Fin n → b) → ℂ)
        (Λ Λ' : Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ →
          Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ),
        IsMaxEntRep da Pa ∧ IsMaxEntRep db Pb ∧ IsLQCC Λ ∧ IsLQCC Λ' ∧
        Λ (pureState (truncatedState TYP p e f)) = pureState Pa ∧
        |Real.logb 2 da / n - entEntropy ψ| < ε + 2 / n ∧
        Λ' (pureState Pb) = pureState (truncatedState TYP p e f) ∧
        |Real.logb 2 db / n - entEntropy ψ| < ε + 1 / n := by sorry

end DHRUniq
