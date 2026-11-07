-- Prove2me | Theorems.Thm_ConsModCount_uniform_fibres
-- name    : ConsModCount.uniform_fibres
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:06.612709+00:00
-- url     : https://prove2.me/theorems/654d8a61-ffa2-4b35-bf71-4b69054dbd77
-- title:
--   Lemma (Uniform fibres on two-element domains) — affine solution sets and uniform fibres
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$ containing every unary subset, with a Mal'tsev polymorphism. Let $I$ be an $H$-instance and $U_v\subseteq D$, $|U_v|\le2$, sets with $\sigma(v)\in U_v$ for every solution $\sigma$ and every variable $v$. Then:
--
--   1. for every family of labellings $\lambda_v:D\to\mathbb F_2$ injective on $U_v$, the labelled solution set $\{(\lambda_v(\sigma(v)))_v\}\subseteq\mathbb F_2^{V}$, when nonempty, is a coset $e+W$ of a linear subspace $W$;
--   2. for every set $S$ of variables, all nonempty fibres of the projection of the solution set to $S$ have the same cardinality;
--   3. for distinct variables $x,y$ the integer matrix $(a,b)\mapsto|\{\sigma:\sigma(x)=a,\ \sigma(y)=b\}|$ is block-rank-one.
--
--   The lemma excludes obstructions all of whose domains have at most two values.
--
--   Differences from the source:
--   - generalization: every variable is restricted to a set of cardinality at most two (by a unary constraint) → every solution takes its value at v in a given set U_v with |U_v| ≤ 2; reason: a unary constraint U_v(v) gives this property, so the statement specializes to the source's
--   - reading: After independently labelling each two-element set by F2 → for every family of labellings injective on the sets U_v; reason: the source's claim holds for any labelling; stated for all of them
--   - reading: a coordinate projection → the projection to an arbitrary set S of variables; reason: the source does not restrict the projection
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §11, Lemma (Uniform fibres on two-element domains), p.17 (PDF p.18)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Uniform fibres on two-element domains)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §11, p.17, PDF p.18). Under the standing
assumption of §§10–13 (`H` conservative): suppose that `H` has a Mal'tsev polymorphism. Consider an
unweighted `H`-gadget in which every variable is restricted to a set of cardinality at most two.
After independently labelling each two-element set by `𝔽₂`, its nonempty solution relation is
affine. Every nonempty fibre of a coordinate projection has the same cardinality. In particular, an
integer count matrix on two single-variable terminals is block-rank-one.

**Formalization Note.** "Restricted to a set `U_v` with `|U_v| ≤ 2`" is the hypothesis that every
solution takes its value at `v` in `U_v` (a unary constraint `U_v(v)` gives it). The labelling is any
family `lab v : D → 𝔽₂` injective on `U_v`; affine means a coset `e + V` of a subspace. A coordinate
projection is the restriction to a set `S` of variables; its fibre through a solution `σ₁` is the set
of solutions agreeing with `σ₁` on `S`. The two terminals are distinct variables `x ≠ y`. -/
theorem uniform_fibres {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D) (hH : Conservative H)
    (hM : HasMaltsev H) (I : Instance H) (U : Fin I.n → Finset D) (hU : ∀ v, (U v).card ≤ 2)
    (hres : ∀ σ, I.Sat σ → ∀ v, σ v ∈ U v) :
    (∀ lab : Fin I.n → D → ZMod 2, (∀ v, Set.InjOn (lab v) (U v)) →
      {x : Fin I.n → ZMod 2 | ∃ σ, I.Sat σ ∧ x = fun v => lab v (σ v)}.Nonempty →
      ∃ (e : Fin I.n → ZMod 2) (V : Submodule (ZMod 2) (Fin I.n → ZMod 2)),
        {x : Fin I.n → ZMod 2 | ∃ σ, I.Sat σ ∧ x = fun v => lab v (σ v)} = {x | x - e ∈ V}) ∧
    (∀ (S : Finset (Fin I.n)) (σ₁ σ₂ : Fin I.n → D), I.Sat σ₁ → I.Sat σ₂ →
      Nat.card {σ : Fin I.n → D // I.Sat σ ∧ ∀ v ∈ S, σ v = σ₁ v} =
        Nat.card {σ : Fin I.n → D // I.Sat σ ∧ ∀ v ∈ S, σ v = σ₂ v}) ∧
    (∀ x y : Fin I.n, x ≠ y →
      BlockRankOne (fun a b : D => Nat.card {σ : Fin I.n → D // I.Sat σ ∧ σ x = a ∧ σ y = b})) := by sorry

end ConsModCount
