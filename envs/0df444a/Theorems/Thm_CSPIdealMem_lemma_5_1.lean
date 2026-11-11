-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_5_1
-- name    : CSPIdealMem.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:54.762255+00:00
-- url     : https://prove2.me/theorems/c5cb3fbf-fa4e-4c16-bb08-bd8c2fc8489d
-- title:
--   Lemma 5.1 — the span coefficients recover polynomial values on any number of variables
-- statement:
--   Let $D\subseteq\mathbb Q$ be nonempty and finite, and suppose
--   $$
--   \nu_d(\mathrm{id}_D)=\sum_{e\in E}\lambda_e\,\nu_d(e),\qquad\lambda_e\in\mathbb Q.\tag{5.1}
--   $$
--   Then for every finite variable set $X$, every assignment $\varphi:X\to D$ and every $f_0\in\mathbb Q[X]_{\le d}$,
--   $$
--   f_0(\varphi)=\sum_{e\in E}\lambda_e\,f_0(e\circ\varphi).\tag{5.2}
--   $$
--   The coefficients are those of (5.1), independent of $X$, $f_0$ and $\varphi$.
--
--   Differences from the source:
--   - encoding: rational coefficients λ_e indexed by e ∈ E (the covered endomorphisms) → a function lam on all maps D → D; all sums run over the covered maps only; reason: values off E never enter, so the two forms are equivalent
--   - encoding: a finite variable set X → any finite type X; reason: the same
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 5.1, (5.1)–(5.2), p.32 (PDF 32)

import Mathlib
import Definitions.Def_CSPIdealMem_EvalSpace

namespace CSPIdealMem

open Classical in
/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 5.1 with (5.1)–(5.2), p.32 (PDF 32).

Suppose (5.1): `ν_d(id_D) = ∑_{e ∈ E} λ_e ν_d(e)` with rational `λ_e` (`E` the covered
endomorphisms). Then for every finite variable set `X`, every assignment `φ : X → D` and every
`f₀ ∈ ℚ[X]_{≤d}`, `f₀(φ) = ∑_{e ∈ E} λ_e f₀(e ∘ φ)` (5.2).

**Formalization Note.** The coefficients are a function `λ` on all maps `D → D`; only its values
on covered endomorphisms enter. -/
theorem lemma_5_1 (D : Finset ℚ) (hD : D.Nonempty) (Γ : ConstraintLanguage D) (d : ℕ)
    (lam : (D → D) → ℚ)
    (h51 : mapVec d id = ∑ e ∈ Finset.univ.filter (IsCovered Γ), lam e • mapVec d e) :
    ∀ (X : Type) [Fintype X] (φ : X → D) (f : MvPolynomial X ℚ), f.totalDegree ≤ d →
      MvPolynomial.eval (fun x => ((φ x : D) : ℚ)) f =
        ∑ e ∈ Finset.univ.filter (IsCovered Γ),
          lam e * MvPolynomial.eval (fun x => ((e (φ x) : D) : ℚ)) f := by sorry

end CSPIdealMem
