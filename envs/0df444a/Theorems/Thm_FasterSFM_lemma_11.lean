-- Prove2me | Theorems.Thm_FasterSFM_lemma_11
-- name    : FasterSFM.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:32.705208+00:00
-- url     : https://prove2.me/theorems/8bafe6f5-f532-4f1d-9cb2-87069333c22e
-- title:
--   Lemma 11 — row insertion makes fixed progress $\gamma/8$ in the potential
-- statement:
--   Let $P$ be an admissible cutting-plane body, $S$ a subspace with orthonormal basis $J$, and $z=Jy$ a certified center (12). Let $b\in S$ be a unit vector with $b^\top z\ge0$, and let $\upsilon=\sqrt{b^\top H_{\mathrm{fl}}(z)^{-1}b/\gamma}$ and $\rho=\upsilon+b^\top z$. If $\upsilon\ge\delta$, append the row $(b,\rho)$ to obtain $P_+$. Then
--
--   1. $\delta B_2^n\subseteq P_+$;
--   2. the potential grows by a fixed amount:
--   $$\min_{P_+\cap S}\Psi_{\mathrm{fl},+}\ \ge\ \min_{P\cap S}\Psi_{\mathrm{fl}}+\frac\gamma8;$$
--   3. a constant number $k_0$ of exact full Newton steps on $\Psi_{S,+}$ from $y$ restores a certified center of $P_+$; $k_0$ is absolute, the same for all data.
--
--   Each wide step therefore raises the potential by a constant, which bounds the number of inserted rows (Lemma 13).
--
--   Differences from the source:
--   - generalization: the oracle's lifted unit normal b → any unit b ∈ S with bᵀz ≥ 0; reason: the proof uses only these properties
--   - generalization: the current subspace S of the algorithm → any subspace (column space of J, JᵀJ = I); reason: reading R8; the current S is an instance
--   - encoding: min over the section P ∩ S of Ψ_fl → Φ(S, P) = infimum of Ψ_fl over the points of S with all slacks positive; reason: Ψ_fl is +∞ on the boundary in the paper, while Lean's log 0 = 0 would be a junk value; Lemma 9 says the infimum is attained
--   - reading: "a constant number of exact full Newton steps restores (12)" → ∃ k₀ ∈ ℕ, chosen before all data, such that the k₀-th full Newton iterate of Ψ_{S,+} from y is a certified center of P₊; reason: the strongest reading of "constant"
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 11, p.22 (υ, ρ on p.21)

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix

/-- **Lemma 11** (Row insertion makes fixed progress), p.22.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 11, p.22 (with `υ`, `ρ` of §5.4, p.21).

"At a certified center z = Jy ∈ P_S, let the separation oracle return a nonzero vector, with lifted
unit normal b ∈ S and bᵀz ≥ 0, and define υ and ρ as above. If υ ≥ δ, append (b, ρ) to the
original-space rows. The new body P₊ still contains δB₂ⁿ, and the new barrier Ψ_{fl,+} satisfies
min_{P₊∩S} Ψ_{fl,+} ≥ min_{P∩S} Ψ_fl + γ/8. A constant number of exact full Newton steps restores
(12)."

Here `υ = (bᵀH_fl(z)⁻¹b/γ)^{1/2}` and `ρ = υ + bᵀz` (p.21).

**Formalization Note.**
* Generalization: `b` is any unit vector of `S` with `bᵀz ≥ 0` (the oracle's lifted normal is one);
  `S` is any subspace, the column space of `J` with `JᵀJ = I` (reading R8).
* `δB₂ⁿ ⊆ P₊`: every `x` with `‖x‖₂ ≤ δ` satisfies all rows of `P₊`.
* The minima over the sections are the potentials `Φ(S, P)` and `Φ(S, P₊)` of (13).
* "A constant number of exact full Newton steps restores (12)": there is one `k₀ ∈ ℕ`, chosen before
  all data, such that the `k₀`-th full Newton iterate of `Ψ_{S,+}` from `y` is a certified center of
  `P₊`. -/
theorem lemma_11 :
    ∃ k₀ : ℕ, ∀ {n N : ℕ} (P : Body n), P.Admissible →
      ∀ (J : Matrix (Fin n) (Fin N) ℝ), Jᵀ * J = 1 →
      ∀ (y : Fin N → ℝ), P.Certified J y →
      ∀ (b : Fin n → ℝ), b ∈ colSpace J → b ⬝ᵥ b = 1 → 0 ≤ b ⬝ᵥ (J *ᵥ y) →
      delta n ≤ P.upsilon (J *ᵥ y) b →
      let Pp : Body n := P.insertRow b (P.upsilon (J *ᵥ y) b + b ⬝ᵥ (J *ᵥ y))
      (∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ delta n ^ 2 → Pp.Mem x) ∧
      P.Phi (colSpace J) + gam / 8 ≤ Pp.Phi (colSpace J) ∧
      Pp.Certified J ((newtonStep (Pp.PsiS J))^[k₀] y) := by sorry

end FasterSFM
