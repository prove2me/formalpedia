-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_11_15_psi
-- name    : DiazModulus.dalag_cor_11_15_psi
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:29.257581+00:00
-- url     : https://prove2.me/theorems/b197af13-ef7c-4dbe-bed0-c02b3d893253
-- title:
--   DALAG Cor. 11.15: for (Q̄, ℒ̃), if V ⊆ ℂᵈ meets Q̄ᵈ only in 0, then dim_Q̄(V ∩ ℒ̃ᵈ) ≤ Ψ(dim V, dₘᵢₙ), with DALAG's table Ψ and dₘᵢₙ the least dimension of a rational S ⊇ V
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   DALAG's function $\Psi$ is given by a table (DALAG, §11.5, p. 394). Here, for natural numbers $a, b$, $\Psi(a, b)$ is defined by the following cases, taken in this order: $\Psi(a, b) = 0$ if $a = 0$; else $\Psi(a, b) = 1$ if $a = 1$ and $b \ge 3$; else $a(a - 1) + 1$ if $a \ge 2$ and $a + 3 \le b$; else $a(a - 1) + 2$ if $a \ge 2$ and $a + 2 = b$; else $a(a + 1)$ if $a + 1 = b$; and $0$ in every remaining case (these are $a \ge 1$ with $b \le a$, outside the table). For $0 < a < b$ the four middle cases are the four rows of the printed table, and $\Psi(0, b) = 0$ for every $b$.
--
--   Let $V \subseteq \mathbb C^d$ be a subspace that contains no non-zero vector with algebraic coordinates, and let $S_0 \supseteq V$ be a rational subspace of least dimension among the rational subspaces containing $V$; write $d_{\min} = \dim S_0$. Then: if $\dim V > 0$, then $\dim V < d_{\min}$; $V \cap \widetilde{\mathcal L}^d$ is a finite-dimensional $\overline{\mathbb Q}$-vector space; and
--   $$\dim_{\overline{\mathbb Q}}\big(V \cap \widetilde{\mathcal L}^d\big) \le \Psi(\dim V, d_{\min}).$$
--   For $\dim V = 0$ the bound is $\Psi(0, d_{\min}) = 0$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), for (K, ℒ) = (Q̄, ℒ̃), with DALAG's bound Ψ(dim V, d_min). DALAG's table of Ψ (p. 394) leaves Ψ(0, 0) undefined. The statement covers dim V = 0 separately, by the value Ψ(0, b) = 0 for every b. The proof follows Roy's route: D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (p. 39), in the form DiazModulus.roy_theorem_five_dmin, and Roy's Lemma (p. 40) through DiazModulus.dalag_psi_floor_roy_phi. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_11_15_psi {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀) (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (0 < Module.finrank ℂ ↥V → Module.finrank ℂ ↥V < Module.finrank ℂ ↥S₀) ∧
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
    Module.finrank (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ≤
      Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S₀) := by
  sorry

end DiazModulus
