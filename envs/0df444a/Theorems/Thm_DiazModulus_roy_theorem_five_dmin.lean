-- Prove2me | Theorems.Thm_DiazModulus_roy_theorem_five_dmin
-- name    : DiazModulus.roy_theorem_five_dmin
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:30.551214+00:00
-- url     : https://prove2.me/theorems/ee3d71c1-6fe6-40c3-8b75-41ecae34ff82
-- title:
--   DALAG Cor. 11.15 for (Q̄, ℒ̃), decomposition form: if V ∩ Q̄ᵈ = 0, then dim_Q̄(V ∩ ℒ̃ᵈ) ≤ Σ nᵢdᵢ/(dᵢ − nᵢ) with (dim V, dₘᵢₙ) = Σ (nᵢ, dᵢ), dₘᵢₙ the least dimension of a rational S ⊇ V
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   A *decomposition* of a pair $(n, d)$ of natural numbers is a finite list $(n_1, d_1), \dots, (n_k, d_k)$ of pairs of natural numbers with $0 < n_i < d_i$ for every $i$, $\sum_i n_i = n$ and $\sum_i d_i = d$ (the empty list, $k = 0$, decomposes $(0, 0)$ only).
--
--   Let $V \subseteq \mathbb C^d$ be a subspace that contains no non-zero vector with algebraic coordinates, and let $S_0 \supseteq V$ be a rational subspace of least dimension among the rational subspaces containing $V$; write $d_{\min} = \dim S_0$. Then $V \cap \widetilde{\mathcal L}^d$ is a finite-dimensional $\overline{\mathbb Q}$-vector space, and there is a decomposition $(n_1, d_1), \dots, (n_k, d_k)$ of $(\dim V, d_{\min})$ with
--   $$\dim_{\overline{\mathbb Q}}\big(V \cap \widetilde{\mathcal L}^d\big) \le \sum_{i=1}^k \frac{n_i d_i}{d_i - n_i}.$$
--   DALAG states the bound as $\Psi(\dim V, d_{\min})$; passing from the decomposition form to $\Psi$ uses Roy's closed form of $\varphi$ (Roy 1992, p. 40) and is not part of this statement. For $d_{\min} = d$ this is Roy's Theorem 5.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), for (K, ℒ) = (Q̄, ℒ̃), in the decomposition form; the case d_min = d is D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (p. 39). The proof follows Roy 1992, Th. 5, not DALAG's argument for Cor. 11.15. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_theorem_five_dmin {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀) (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥V ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S₀ ∧
      (Module.finrank (↥Qbar)
          ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) : ℚ) ≤
        (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  sorry

end DiazModulus
