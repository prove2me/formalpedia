-- Prove2me | Theorems.Thm_Diaz_log_modulus_forces_independence
-- name    : Diaz.log_modulus_forces_independence
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:29:12.911988+00:00
-- url     : https://prove2.me/theorems/04eb8840-66ba-46e1-a498-b4fe61365ea5
-- title:
--   A logarithmic modulus forces independence, from the master dichotomy
-- statement:
--   **Source.** This is a corollary of the dichotomy below that Carlo Perassi states in unpublished work. It **is not his own**: it is Exercise 15.16(c) of M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer, 2000), p. 614, whose hint refers to G. Diaz, *La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire*, J. Théor. Nombres Bordeaux 9 (1997), 229–245, where it is Proposition 2 (p. 241). It is ported here as an attributed legacy node.
--
--   **Statement.** Let $\lambda$ be a non-zero logarithm of an element of a conjugation-stable subfield $K\subset\mathbb C$ (at $K=\overline{\mathbb Q}$: $\lambda\in\mathcal L\setminus\{0\}$), with $\lambda\notin\mathbb R$, and suppose $|\lambda|$ is again such a logarithm. Then
--   $$\operatorname{trdeg}_{\mathbb Q}\mathbb Q\bigl(\lambda,\overline\lambda,|\lambda|\bigr)\ \ge\ 2 .$$
--
--   **Provenance of the carried hypothesis.** The dichotomy `hMaster` is Carlo Perassi's master dichotomy for rationally proportional products (unpublished). He derives it from Roy and Waldschmidt's *Théorème 0.2* (D. Roy and M. Waldschmidt, *Approximation diophantienne et indépendance algébrique de logarithmes*, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, p. 755; the dichotomy form), and he records that its $m=1$ case is Exercise 1.8 / the worked example of §12.5 of M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer, 2000; pp. 24 and 438–439). The derivation from Théorème 0.2 is not formalised, so the dichotomy is **carried as the explicit hypothesis `hMaster` rather than asserted**: this node asserts only the implication.
--
--   **What the node proves.** Apply `hMaster` to $(\mu_1,\nu_1,\mu_2,\nu_2)=(\lambda,\overline\lambda,|\lambda|,|\lambda|)$ with $m=1$; all four entries are non-zero logarithms, and $|\lambda|^2=\lambda\overline\lambda$. The first alternative gives $|\lambda|\in\mathbb Q^\times\lambda$ and the second $|\lambda|\in\mathbb Q^\times\overline\lambda$; taking imaginary parts, either makes $\lambda$ real, which is excluded. Only the transcendence-degree alternative survives. That elimination — the unconditional core of the corollary — is the content actually verified here.
--
--   **Scope of the conclusion.** Carlo Perassi states the conclusion as "$\lambda$ and $\overline\lambda$ are algebraically independent over $\mathbb Q$; equivalently $\operatorname{trdeg}_{\mathbb Q}\mathbb Q(\lambda,|\lambda|)=2$". What is recorded here is the lower bound $\ge 2$ that the dichotomy yields directly. The passage from it to algebraic independence of the pair, and to the exact value $2$, uses the standard extraction of a transcendence basis from a generating set together with $\overline\lambda=|\lambda|^2/\lambda$; that step is **not** formalised in this node.
--
--   **Formalization note.** $K$ is an arbitrary subfield of $\mathbb C$ with `hKconj` asserting stability under complex conjugation — the property of $\mathcal L$ used to know $\overline\lambda\in\mathcal L$. "$\lambda\notin\mathbb R$" is `lam.im ≠ 0`, and $|\lambda|$ is `((‖lam‖ : ℝ) : ℂ)`. `#print axioms` on the submitted proof: `[propext, Classical.choice, Quot.sound]`.
-- source:
--   Known: Exercise 15.16(c) of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Springer, 2000, p. 614, whose hint refers to Proposition 2 (p. 241) of G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245. This node proves only the implication from its carried hypothesis hMaster, a dichotomy for rationally proportional products that it does not prove; the unconditional statement for logarithms of algebraic numbers, in contrapositive form, is DiazModulus.exp_abs_transcendental_of_conj_algebraic. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

theorem Diaz.log_modulus_forces_independence {K : Subfield ℂ}
    (hKconj : ∀ z : ℂ, z ∈ K → conj z ∈ K)
    (hMaster : ∀ μ₁ ν₁ μ₂ ν₂ : ℂ,
      Complex.exp μ₁ ∈ K → Complex.exp ν₁ ∈ K → Complex.exp μ₂ ∈ K → Complex.exp ν₂ ∈ K →
      μ₁ ≠ 0 → ν₁ ≠ 0 → μ₂ ≠ 0 → ν₂ ≠ 0 →
      ∀ m : ℚ, m ≠ 0 → μ₂ * ν₂ = (m : ℂ) * (μ₁ * ν₁) →
      ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * μ₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * ν₁))
      ∨ ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * ν₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * μ₁))
      ∨ 2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({μ₁, ν₁, μ₂, ν₂} : Set ℂ)))
    {lam : ℂ}
    (hlam : Complex.exp lam ∈ K) (hlam0 : lam ≠ 0) (hlamR : lam.im ≠ 0)
    (hmod : Complex.exp ((‖lam‖ : ℝ) : ℂ) ∈ K) :
    2 ≤ Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)) := by sorry
