-- Prove2me | Theorems.Thm_DeepSets_Supplement_theorem_9_universal_approximation
-- name    : DeepSets.Supplement.theorem_9_universal_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:27:19.522181+00:00
-- url     : https://prove2.me/theorems/d8e3cc41-6877-5f26-9259-c1dd96150ee0
-- title:
--   Theorem 9 — $\rho\left(\sum_{x\in X}\phi(x)\right)$ uniformly approximates continuous invariant functions of $M$ elements of a compact $K\subseteq\mathbb R^d$
-- statement:
--   Fix $d\ge 0$, a set size $M\ge 0$ and a compact set $K\subseteq\mathbb R^d$. Let $f$ be a real-valued function of $M$ vectors that is continuous and permutation invariant on $K^M$. Then for every $\varepsilon>0$ there are a finite $L$, a polynomial map $\phi:\mathbb R^d\to\mathbb R^L$ and a polynomial $\rho:\mathbb R^L\to\mathbb R$ such that
--   $$
--   \Bigl|f(x_1,\dots,x_M)-\rho\Bigl(\sum_{m=1}^{M}\phi(x_m)\Bigr)\Bigr|<\varepsilon\qquad\text{for all }(x_1,\dots,x_M)\in K^M .
--   $$
--   This is the universal approximation property of the Deep Sets architecture for elements of any dimension: at a fixed set size, sums of per-element features followed by a readout approximate every continuous set function on a compact universe, uniformly. It is a companion theorem and is not used in the proof of Theorem 2.
--
--   **Formalization Note** The map $\phi$ is a family of $L$ elements of `MvPolynomial (Fin d) ℝ` and $\rho$ is an element of `MvPolynomial (Fin L) ℝ`, both evaluated by `MvPolynomial.eval`. The number $L$, like $\phi$ and $\rho$, may depend on $f$ and $\varepsilon$. The set $K$ may be empty, and the tuples may repeat an element.
--
--   Differences from the source:
--   - reading: "can be approximated arbitrarily close" → for every ε > 0 the error is below ε at every point of K^M (uniform approximation on the compact domain); reason: the proof invokes Stone–Weierstrass, which is uniform approximation on a compact set; this is stronger than pointwise approximation
--   - reading: "for suitable transformations φ and ρ" → polynomial maps φ from ℝ^d to ℝ^L and ρ from ℝ^L to ℝ, with L finite; reason: the proof constructs polynomials ("all symmetric polynomials can be written in the form required by the theorem"); with arbitrary maps the claim has no content, and polynomial maps are the stronger reading, since they are in particular suitable transformations
--   - generalization: a continuous function f : ℝ^{d×M} → ℝ which is permutation invariant → f continuous and permutation invariant on K^M only; reason: a function continuous and invariant on all of ℝ^{d×M} is so on K^M, so the printed case is included
--   - encoding: a set X of fixed size M of elements of a compact set, with the sum of φ(x) over x ∈ X → a tuple x : Fin M → (Fin d → ℝ) with entries in K, repeats allowed, and the sum of φ(x m) over m; reason: the domain of f is printed as ℝ^{d×M}, whose points are tuples; a sum over the set of values would lose multiplicities
--   - encoding: a compact set in ℝ^d and a set size fixed to M → any d : ℕ, any M : ℕ and any compact K, including d = 0, M = 0 and K empty; reason: the page excludes none of these; the statement holds trivially when K^M is empty or a single point
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, Theorem 9, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_DeepSets_Supplement_IsPermInvariantOn

namespace DeepSets.Supplement

/-- **Theorem 9** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.2, p.15). Assume the elements
are from a compact set in `ℝ^d` and the set size is fixed to `M`. Then any continuous function
`f : ℝ^{d×M} → ℝ` which is permutation invariant to the elements can be approximated arbitrarily
close in the form `ρ(∑_{x ∈ X} φ(x))`, for suitable transformations `φ` and `ρ`.

**Formalization Note**
* "Arbitrarily close" is uniform on the compact set `K^M`, as in the Stone–Weierstrass theorem
  that the proof invokes.
* The "suitable transformations" are the polynomial maps of the proof: `φ : ℝ^d → ℝ^L` is given
  by `L` polynomials in `d` variables and `ρ : ℝ^L → ℝ` is a polynomial in `L` variables, for a
  finite `L` that may depend on `f` and `ε`. With arbitrary maps the statement would have no
  content, since every invariant function could then be represented exactly.
* An input is a tuple `x : Fin M → (Fin d → ℝ)` of elements of `K`, repeated entries allowed, and
  `∑_{x ∈ X} φ(x)` is `∑_m φ(x_m)`, with multiplicity. Continuity and invariance of `f` are
  assumed on `K^M` only, which contains the printed case of an `f` continuous on `ℝ^{d×M}`. -/
theorem theorem_9_universal_approximation (d M : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (f : (Fin M → Fin d → ℝ) → ℝ)
    (hf_cont : ContinuousOn f (Set.univ.pi fun _ : Fin M => K))
    (hf_inv : IsPermInvariantOn K f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℕ) (φ : Fin L → MvPolynomial (Fin d) ℝ) (ρ : MvPolynomial (Fin L) ℝ),
      ∀ x ∈ Set.univ.pi (fun _ : Fin M => K),
        |f x - MvPolynomial.eval (∑ m, fun l => MvPolynomial.eval (x m) (φ l)) ρ| < ε := by sorry

end DeepSets.Supplement
