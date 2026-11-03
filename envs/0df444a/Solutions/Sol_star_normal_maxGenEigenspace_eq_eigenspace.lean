-- Prove2me | solution 1 for star_normal_maxGenEigenspace_eq_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:21:00.088597+00:00
-- url     : https://prove2.me/submissions/ec8e131f-6d34-4914-8b5d-864b6599547d

import Mathlib

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_StarNormalEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


noncomputable section AristotleLemmas

/-
For a star-normal operator f, the kernel of f^2 is equal to the kernel of f.
-/
lemma IsStarNormal.ker_sq_eq_ker {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (f : Module.End ℂ A) (hf : IsStarNormal f) :
    LinearMap.ker (f ^ 2) = LinearMap.ker f := by
      -- Let's take an element x in the kernel of f squared. Then f(f(x)) = 0.
      have h1 : ∀ x, f (f x) = 0 → f x = 0 := by
        -- Since $f$ is star-normal, we have $f^* f = f f^*$. Therefore, $f^*(f(x)) = f(f^*(x))$.
        have h_comm : ∀ x, f.adjoint (f x) = f (f.adjoint x) := by
          -- Since $f$ is star-normal, we have $f * f^* = f^* * f$. Therefore, for any $x$, $f(f^*(x)) = f^*(f(x))$.
          have h_comm : f * f.adjoint = f.adjoint * f := by
            cases hf;
            (expose_names; exact id (Commute.symm star_comm_self));
          exact fun x => by simpa using congr_arg ( fun g => g x ) h_comm.symm;
        -- Since $f$ is star-normal, we have $f^* f = f f^*$. Therefore, $f^*(f(x)) = f(f^*(x))$. Applying $f^*$ to both sides of $f(f(x)) = 0$, we get $f^*(f(f(x))) = f^*(0) = 0$.
        have h_apply_adjoint : ∀ x, f (f x) = 0 → f.adjoint (f x) = 0 := by
          intro x hx
          have h_apply_adjoint : inner ℂ (f.adjoint (f x)) (f.adjoint (f x)) = inner ℂ (f x) (f (f.adjoint (f x))) := by
            rw [ ← LinearMap.adjoint_inner_right ];
            rw [ LinearMap.adjoint_adjoint ];
          simp_all +decide [ ← h_comm ];
        intro x hx
        have h_inner : inner ℂ (f x) (f x) = inner ℂ x (f.adjoint (f x)) := by
          rw [ LinearMap.adjoint_inner_right ];
        simp_all +decide [ inner_self_eq_norm_sq_to_K ];
      aesop

end AristotleLemmas

lemma star_normal_maxGenEigenspace_eq_eigenspace_oai  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {f: Module.End ℂ A} (hf: IsStarNormal f) {k: ℂ}:
    f.maxGenEigenspace k = f.eigenspace k := by
  apply le_antisymm;
  · intro x hx
    aesop;
    -- Since $f$ is star-normal, we have $\ker((f - kI)^2) = \ker(f - kI)$.
    have h_ker_sq_eq_ker : LinearMap.ker ((f - k • 1) ^ 2) = LinearMap.ker (f - k • 1) := by
      apply IsStarNormal.ker_sq_eq_ker;
      -- Since $f$ is star-normal, we have $f * star f = star f * f$. Therefore, $(f - k • 1) * star (f - k • 1) = star (f - k • 1) * (f - k • 1)$.
      have h_star_normal : (f - k • 1) * star (f - k • 1) = star (f - k • 1) * (f - k • 1) := by
        simp_all +decide [ sub_mul, mul_sub, smul_sub, sub_smul ];
        simp_all +decide [ sub_eq_iff_eq_add, IsStarNormal, smul_smul ];
        simp_all +decide [ mul_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm ];
        exact Eq.symm (star_comm_self' f);
      exact (isStarNormal_iff (f - k • 1)).mpr (id (Eq.symm h_star_normal));
    -- By induction on $w$, we can show that $\ker((f - kI)^w) = \ker(f - kI)$ for all $w \geq 1$.
    have h_ker_pow_eq_ker : ∀ w ≥ 1, LinearMap.ker ((f - k • 1) ^ w) = LinearMap.ker (f - k • 1) := by
      intro w hw
      induction' w, Nat.succ_le.mpr hw using Nat.le_induction with w hw ih;
      · simp +decide;
      · simp_all +decide [ pow_succ, LinearMap.ker_comp ];
        simp_all +decide [ SetLike.ext_iff, LinearMap.mem_ker ];
        intro x; specialize ih ( f x - k • x ) ; simp_all +decide [ sub_eq_iff_eq_add, pow_succ, mul_sub, sub_mul ] ;
    by_cases hw : 1 ≤ w <;> aesop;
    replace h_ker_pow_eq_ker := SetLike.ext_iff.mp ( h_ker_pow_eq_ker w hw ) x; aesop;
    exact eq_of_sub_eq_zero h_ker_pow_eq_ker;
  · exact Module.End.eigenspace_le_maxGenEigenspace
end

theorem solution.{u_1} : type_of% @star_normal_maxGenEigenspace_eq_eigenspace_oai.{u_1} := @star_normal_maxGenEigenspace_eq_eigenspace_oai.{u_1}
