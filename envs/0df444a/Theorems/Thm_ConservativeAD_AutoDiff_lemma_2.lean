-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_lemma_2
-- name    : ConservativeAD.AutoDiff.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:52.786974+00:00
-- url     : https://prove2.me/theorems/655e7e3b-29aa-4094-91aa-9970ea4d5c81
-- title:
--   Lemma 2 — a closed, locally bounded field is conservative for $f$ iff the chain rule (5) holds
-- statement:
--   Let $D:\mathbb R^n\rightrightarrows\mathbb R^n$ be a locally bounded set-valued map with closed graph and nonempty values, and let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz. Then $D$ is a conservative field for $f$ (Definition 2) if and only if for every absolutely continuous curve $x:[0,1]\to\mathbb R^n$, for almost every $t\in[0,1]$, $t\mapsto f(x(t))$ is differentiable at $t$ and
--
--   $$
--   \frac{d}{dt}f(x(t))=\langle v,\dot x(t)\rangle\qquad\text{for all } v\in D(x(t)). \tag{5}
--   $$
--
--   The lemma characterizes conservativity by the chain rule. It turns the chain-rule calculus of conservative mappings (Lemmas 3–5) into statements about conservative fields.
--
--   **Formalization Note** The hypothesis that $D$ has nonempty values is added: the paper's Lemma 2 omits it, but Definition 1 requires it, and for $D\equiv\emptyset$ condition (5) holds vacuously while $D$ is not conservative. Compactness of the values follows from closed graph and local boundedness. Differentiability is asserted with `HasDerivAt`.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 8, Lemma 2, eq. (5)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeField
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap

namespace ConservativeAD.AutoDiff

/-- Lemma 2 (chain rule and conservativity), p. 8. For a locally bounded, graph-closed set-valued
map `D : ℝ^n ⇒ ℝ^n` with nonempty values (added: Definition 1 requires nonempty values, and for
`D ≡ ∅` the right side holds vacuously) and a locally Lipschitz `f`, `D` is a conservative field
for `f` iff the chain rule (5) holds along every absolutely continuous curve. -/
theorem lemma_2 {n : ℕ} (D : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hlb : IsLocallyBounded D)
    (hcl : IsClosed {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | z.2 ∈ D z.1})
    (hne : ∀ x, (D x).Nonempty)
    (hf : LocallyLipschitz f) :
    ConservativeAD.GradAE.IsPotential D f ↔ HasChainRule D f := by sorry

end ConservativeAD.AutoDiff
