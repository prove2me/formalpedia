-- Prove2me | Theorems.Thm_DiffVI_Cone_theorem_8_1
-- name    : DiffVI.Cone.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:37.917325+00:00
-- url     : https://prove2.me/theorems/a992d13e-bc32-4d90-a8d2-3d22e6c5a5e3
-- title:
--   Theorem 8.1, p. 61 — for a cone K, under (A), (B), (D), (C′), Ψ(0) = 0 and (E), the iterates of (7.2) exist, are unique, and satisfy (7.5) and (7.6)
-- statement:
--   Let $K$ be a closed convex cone in $\mathbb R^m$ and $\theta\in[0,1]$. Let $(f,B,G)$ satisfy (A), (B) and (D) on $[0,T]\times\mathbb R^n$, let $F=E^\top\circ\Psi\circ E$ satisfy (C′), and assume $\Psi(0)=0$ and condition (E). For an integer $N\ge1$ write $h=T/N$. Then there are an integer $\bar N\ge1$ (that is, $\bar h=T/\bar N$), positive constants $c_{0,x},c_{1,x},c_{0,u},c_{1,u}$ and an integer $N_1$ such that for every $x^0\in\mathbb R^n$ with $\mathrm{SOL}(K,G(0,x^0)+F)\ne\emptyset$:
--
--   1. for every $N\ge\bar N$ the scheme (7.2) has a run from $x^0$, and any two runs agree in $(x^{h,i},u^{h,i})$ for $i=1,\dots,N$;
--   2. for every $N\ge N_1$, every run satisfies, for $i=0,\dots,N-1$,
--   $$\|x^{h,i+1}\|\le c_{0,x}+c_{1,x}\|x^0\|,\qquad\|u^{h,i+1}\|\le c_{0,u}+c_{1,u}\|x^0\|;\tag{7.5}$$
--   3. there are $c_{2,u}>0$ and $N_2$ such that for every $N\ge N_2$ and every run with $u^{h,0}\in\mathrm{SOL}(K,G(0,x^0)+F)$,
--   $$\|Eu^{h,i+1}-Eu^{h,i}\|\le h\,c_{2,u},\qquad i=0,\dots,N-1.\tag{7.6}$$
--
--   Here (7.2) is $x^{h,i+1}=x^{h,i}+h[f(t_{h,i+1},\theta x^{h,i}+(1-\theta)x^{h,i+1})+B(t_{h,i},x^{h,i})u^{h,i+1}]$, $u^{h,i+1}\in\mathrm{SOL}(K,G(t_{h,i+1},x^{h,i+1})+F)$, with $x^{h,0}=x^0$ and $t_{h,i}=ih$.
--
--   These are exactly the hypotheses (7.5) and case (a) of Theorem 7.1, so the discrete trajectories have uniform/weak-$L^2$ limit points that are weak solutions of the initial-value DVI.
--
--   **Formalization Note** The step sizes $h\in(0,\bar h]$ with $(N_h+1)h=T$ are $h=T/N$, $N\ge\bar N$; "for all $h$ sufficiently small" is "for all $N\ge N_1$". $G(t_0,x^0)$ is $G(0,x^0)$. The constant $\eta_\Upsilon$ of the page is not a hypothesis: under (C′) a constant satisfying (8.7) always exists (p. 57). The initial multiplier $u^{h,0}$ is an arbitrary element of $\mathrm{SOL}(K,G(0,x^0)+F)$, as the proof takes it; uniqueness is claimed for the computed iterates $i\ge1$. The constants $c_{0,x},c_{1,x},c_{0,u},c_{1,u}$ are chosen before $x^0$, as the proof (via (8.14) and Lemma 7.2) gives them; $c_{2,u}$ is chosen after $x^0$, because the proof's constant depends on $\|x^0\|$ and on $u^{h,0}$. The page's last sentence ("Consequently, the conclusion of Theorem 7.1 holds …") is omitted: it is Theorem 7.1(a) applied to these bounds, and Theorem 7.1 is posed in the companion mission *Differential Variational Inequalities 2*.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 61, Theorem 8.1 (without its last sentence); (7.2), (7.5), (7.6) on pp. 42, 44

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem theorem_8_1 {n m ℓ : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B) (ηG : ℝ) (hD : CondD T B G ηG)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ))
    (hC' : CondC' F E Ψ) (hΨ0 : Ψ 0 = 0) (hE : CondE K E) :
    ∃ Nbar : ℕ, 1 ≤ Nbar ∧
    ∃ c0x c1x c0u c1u : ℝ, 0 < c0x ∧ 0 < c1x ∧ 0 < c0u ∧ 0 < c1u ∧ ∃ N1 : ℕ,
    ∀ x0 : EuclideanSpace ℝ (Fin n), (viSol (fun v => G 0 x0 + F v) K).Nonempty →
      (∀ N : ℕ, Nbar ≤ N →
        (∃ (xs : ℕ → EuclideanSpace ℝ (Fin n)) (us : ℕ → EuclideanSpace ℝ (Fin m)), DiffVI.Conv.IsScheme K f B G F T θ x0 N xs us) ∧
        (∀ (xs xs' : ℕ → EuclideanSpace ℝ (Fin n)) (us us' : ℕ → EuclideanSpace ℝ (Fin m)),
          DiffVI.Conv.IsScheme K f B G F T θ x0 N xs us → DiffVI.Conv.IsScheme K f B G F T θ x0 N xs' us' →
            ∀ i, 1 ≤ i → i ≤ N → xs i = xs' i ∧ us i = us' i)) ∧
      (∀ N : ℕ, N1 ≤ N → ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n)) (us : ℕ → EuclideanSpace ℝ (Fin m)), DiffVI.Conv.IsScheme K f B G F T θ x0 N xs us →
        ∀ i < N, ‖xs (i + 1)‖ ≤ c0x + c1x * ‖x0‖ ∧ ‖us (i + 1)‖ ≤ c0u + c1u * ‖x0‖) ∧
      ∃ c2u : ℝ, 0 < c2u ∧ ∃ N2 : ℕ,
        ∀ N : ℕ, N2 ≤ N → ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n)) (us : ℕ → EuclideanSpace ℝ (Fin m)), DiffVI.Conv.IsScheme K f B G F T θ x0 N xs us →
          us 0 ∈ viSol (fun v => G 0 x0 + F v) K →
          ∀ i < N, ‖E (us (i + 1)) - E (us i)‖ ≤ (T / N) * c2u := by sorry

end DiffVI.Cone
