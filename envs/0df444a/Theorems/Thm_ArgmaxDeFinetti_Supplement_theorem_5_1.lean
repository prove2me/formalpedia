-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_5_1
-- name    : ArgmaxDeFinetti.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:44:57.044217+00:00
-- url     : https://prove2.me/theorems/2324b14c-18f8-4adb-9902-6e214f3310b6
-- title:
--   Theorem 5.1, p.37 — $(\sqrt{d-1}/(2n),0)$-disentanglers, and $(\varepsilon,0)$-disentanglers with $\log D=O_\varepsilon(\sqrt d\log d)$
-- statement:
--   1. Let $d\ge2$ and $n\ge1$, and set $\mathcal H_A=\mathcal H_B=\mathbb C^d$. There is a channel
--   $$
--   \Lambda_{d,n}:D\big(\mathcal H_A^{\otimes n}\otimes\mathcal H_B^{\otimes n}\big)\to D(\mathcal H_A\otimes\mathcal H_B)
--   $$
--   which is an $(\varepsilon_{d,n},0)$-disentangler, where $\varepsilon_{d,n}=\sqrt{d-1}/(2n)$.
--   2. For every $\varepsilon\in(0,1)$ there is a constant $C_\varepsilon$ such that for every $d\ge2$ there is an $(\varepsilon,0)$-disentangler $\Lambda:D(\mathbb C^D)\to D(\mathbb C^d\otimes\mathbb C^d)$ whose input dimension satisfies
--   $$
--   \log D\le C_\varepsilon\sqrt d\,\log d .
--   $$
--
--   In particular $(\varepsilon,\delta)=(1/4,0)$ is achievable with $\log D=O(\sqrt d\log d)$. The original Watrous disentangler conjecture predicted $\log D=\Omega(d)$ for fixed $\varepsilon,\delta$ with $\varepsilon+\delta<1$, so part 2 disproves it.
--
--   **Formalization Note** Channels are linear, completely positive, trace-preserving maps on matrices; the disentangler conditions are (5.1)–(5.2), with the coverage infimum written without a default value.
--
--   Differences from the source:
--   - reading: log D = O_ε(√d log d) → ∃ C (depending on ε only) ∀ d ≥ 2, log D ≤ C·√d·log d; reason: O_ε denotes a constant depending on ε only (standing assumption); since √d log d ≥ √2 log 2 > 0 for d ≥ 2, a bound for all d ≥ 2 is the same as an eventual one
--   - encoding: sup_ρ D_tr(Λ(ρ), SEP) ≤ ε; sup_σ inf_ρ D_tr(Λ(ρ), σ) ≤ δ → D_tr(Λ(ρ), SEP) ≤ ε for every input state ρ; for every σ ∈ SEP and η > 0 some input state ρ has D_tr(Λ(ρ), σ) ≤ δ + η; reason: the same conditions; avoids the default value of an empty infimum
--   - encoding: channel D(ℂ^D) → D(ℂ^d ⊗ ℂ^d) → a ℂ-linear map on matrices satisfying the published WildeQIT.EntBreaking.IsQuantumChannel (completely positive, trace preserving); input index (Fin n → Fin d) × (Fin n → Fin d) in part 1, Fin D in part 2; reason: Lean convention for the paper's channels
--   - encoding: "In particular, one may take (ε, δ) = (1/4, 0)" → not stated separately; reason: it is part 2 at ε = 1/4
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 5.1, eq. (5.3), p.37 (= Theorem 1.6, p.8); definitions (5.1)–(5.2), pp.36–37

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_Supplement_IsDisentangler

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 5.1 (Subexponential disentanglers)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.37, eq. (5.3) (= Theorem 1.6, p.8).
(i) Let `d ≥ 2`, `n ≥ 1` and `H_A = H_B = ℂ^d`. There is a channel `Λ_{d,n} : D(H_A^{⊗n} ⊗ H_B^{⊗n}) → D(H_A ⊗ H_B)`
which is an `(ε_{d,n}, 0)`-disentangler, `ε_{d,n} = √(d − 1)/(2n)`.
(ii) Consequently, for every fixed `ε ∈ (0, 1)` there is an `(ε, 0)`-disentangler with input dimension `D`
satisfying `log D = O_ε(√d log d)`.

**Formalization Note** The input space `H_A^{⊗n} ⊗ H_B^{⊗n}` of (i) is indexed by `(Fin n → Fin d) × (Fin n → Fin d)`.
In (ii) `O_ε` is a constant `C` depending on `ε` only, chosen before `d`, and the input space is `ℂ^D`
(`Fin D`); `log` is natural (another base changes only `C`). The paper's "in particular, one may take
`(ε, δ) = (1/4, 0)`" is (ii) at `ε = 1/4`. The disentangler property is `IsDisentangler` ((5.1)–(5.2)). -/
theorem theorem_5_1 :
    (∀ d n : ℕ, 2 ≤ d → 1 ≤ n →
      ∃ Λ : Matrix ((Fin n → Fin d) × (Fin n → Fin d)) ((Fin n → Fin d) × (Fin n → Fin d)) ℂ →ₗ[ℂ]
          Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
        IsDisentangler Λ (Real.sqrt ((d : ℝ) - 1) / (2 * n)) 0) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      ∃ (D : ℕ) (Λ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        IsDisentangler Λ ε 0 ∧ Real.log D ≤ C * Real.sqrt d * Real.log d) := by sorry

end Supplement

end ArgmaxDeFinetti
